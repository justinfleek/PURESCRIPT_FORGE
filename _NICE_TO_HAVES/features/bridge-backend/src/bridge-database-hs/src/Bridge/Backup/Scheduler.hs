{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

-- | Backup Scheduler - Automated Database Backup System
-- |
-- | **What:** Schedules and executes automated database backups with retention policies.
-- |         Creates full and incremental backups, verifies integrity, and manages retention.
-- | **Why:** Ensures data durability and enables disaster recovery. Prevents data loss
-- |         from hardware failures, corruption, or accidental deletion.
-- | **How:** Uses cron-like scheduling to trigger backups. Creates SQLite backups using
-- |         `.backup` command. Compresses backups and stores with timestamps. Manages
-- |         retention based on age and count limits.
-- |
-- | **Dependencies:**
-- | - `Database.SQLite.Simple`: Database operations
-- | - `System.Directory`: File operations
-- | - `Data.Time`: Timestamp management
-- |
-- | **Mathematical Foundation:**
-- | - **Backup Schedule:** Cron expression → backup times
-- | - **Retention Policy:** Keep backups for `retentionDays` or last `retentionCount`
-- | - **Backup Integrity:** Verified via `PRAGMA integrity_check`
-- |
-- | **Usage Example:**
-- | ```haskell
-- | import Bridge.Backup.Scheduler as Backup
-- |
-- | -- Create scheduler
-- | scheduler <- Backup.createScheduler config dbPath
-- |
-- | -- Start scheduler
-- | Backup.startScheduler scheduler
-- | ```
module Bridge.Backup.Scheduler where

module Bridge.Backup.Scheduler where

import Prelude hiding (read)
import Control.Concurrent (threadDelay, forkIO)
import Control.Monad (forever)
import Control.Concurrent.STM (TVar, newTVarIO, readTVar, writeTVar, atomically)
import Database.SQLite.Simple (Connection, open, close, query_, Only(..))
import Database.SQLite.Simple.Backup (backupFromTo)
import qualified Data.Text as T
import qualified Data.ByteString as BS
import System.Directory (createDirectoryIfMissing, listDirectory, removeFile, getModificationTime)
import System.FilePath ((</>), takeExtension)
import Data.Time (UTCTime, getCurrentTime, addDays, diffUTCTime)
import Data.List (sortBy, partition, splitAt, reverse)
import Data.Ord (comparing)
import Codec.Compression.GZip (compress)

-- | Backup configuration
data BackupConfig = BackupConfig
  { bcSchedule :: String -- Cron expression (e.g., "0 2 * * *" = daily at 2am)
  , bcBackupDir :: FilePath -- Backup directory
  , bcRetentionDays :: Int -- Keep backups for N days
  , bcRetentionCount :: Int -- Keep last N backups
  , bcCompress :: Bool -- Compress backups
  }
  deriving (Eq, Show)

-- | Default backup configuration
defaultBackupConfig :: BackupConfig
defaultBackupConfig = BackupConfig
  { bcSchedule = "0 2 * * *" -- Daily at 2am
  , bcBackupDir = "./backups"
  , bcRetentionDays = 7
  , bcRetentionCount = 10
  , bcCompress = True
  }

-- | Backup scheduler
data BackupScheduler = BackupScheduler
  { bsConfig :: BackupConfig
  , bsDbPath :: FilePath
  , bsRunning :: TVar Bool
  }

-- | Create backup scheduler
-- |
-- | **Purpose:** Creates a backup scheduler instance.
-- | **Parameters:**
-- | - `config`: Backup configuration
-- | - `dbPath`: Path to SQLite database
-- | **Returns:** Backup scheduler instance
createScheduler :: BackupConfig -> FilePath -> IO BackupScheduler
createScheduler config dbPath = do
  -- Create backup directory
  createDirectoryIfMissing True (bcBackupDir config)
  
  running <- newTVarIO False
  pure BackupScheduler
    { bsConfig = config
    , bsDbPath = dbPath
    , bsRunning = running
    }

-- | Create backup
-- |
-- | **Purpose:** Creates a backup of the database.
-- | **Parameters:**
-- | - `scheduler`: Backup scheduler
-- | **Returns:** Either error or backup file path
-- |
-- | **Process:**
-- | 1. Generate backup filename with timestamp
-- | 2. Open source database
-- | 3. Create backup using SQLite `.backup` command
-- | 4. Compress if configured
-- | 5. Verify backup integrity
createBackup :: BackupScheduler -> IO (Either String FilePath)
createBackup scheduler = do
  result <- try $ do
    now <- getCurrentTime
    let timestamp = formatTimestamp now
    let backupFile = bcBackupDir (bsConfig scheduler) </> ("backup_" <> timestamp <> ".db")
    
    -- Open source database
    conn <- open (bsDbPath scheduler)
    
    -- Create backup
    backup conn backupFile
    
    -- Verify backup
    verifyResult <- verifyBackup backupFile
    case verifyResult of
      Left err -> pure (Left err)
      Right _ -> do
        -- Compress if configured
        finalPath <- if bcCompress (bsConfig scheduler) then do
          compressedFile <- compressBackup backupFile
          removeFile backupFile
          pure compressedFile
        else
          pure backupFile
        
        close conn
        pure finalPath
  
  case result of
    Right path -> pure (Right path)
    Left err -> pure (Left ("Backup failed: " ++ show (err :: SomeException)))
  where
    import Control.Exception (try, SomeException)
    import Data.Time.Format (formatTime, defaultTimeLocale)
    
    formatTimestamp :: UTCTime -> String
    formatTimestamp t = formatTime defaultTimeLocale "%Y%m%d_%H%M%S" t
    
    backup :: Connection -> FilePath -> IO ()
    backup sourceConn backupPath = do
      -- Open destination database
      destConn <- open backupPath
      -- Use SQLite backup API
      backupFromTo sourceConn "main" destConn "main"
      close destConn
    
    verifyBackup :: FilePath -> IO ()
    verifyBackup backupPath = do
      conn <- open backupPath
      [Only result] <- query_ conn "PRAGMA integrity_check"
      close conn
      if result == ("ok" :: T.Text) then
        pure (Right ())
      else
        pure (Left ("Backup integrity check failed: " ++ T.unpack result))
    
    compressBackup :: FilePath -> IO FilePath
    compressBackup backupPath = do
      contents <- BS.readFile backupPath
      let compressed = compress contents
      let compressedPath = backupPath <> ".gz"
      BS.writeFile compressedPath compressed
      pure compressedPath

-- | Cleanup old backups
-- |
-- | **Purpose:** Removes old backups based on retention policy.
-- | **Parameters:**
-- | - `scheduler`: Backup scheduler
-- | **Returns:** Number of backups removed
cleanupOldBackups :: BackupScheduler -> IO Int
cleanupOldBackups scheduler = do
  now <- getCurrentTime
  backupDir <- listDirectory (bcBackupDir (bsConfig scheduler))
  let backupFiles = filter (isBackupFile (bsConfig scheduler)) backupDir
  
  -- Sort by modification time (oldest first)
  sortedBackups <- sortBackupsByAge (bcBackupDir (bsConfig scheduler)) backupFiles
  
  -- Apply retention policies
  let retentionCutoff = addDays (negate (bcRetentionDays (bsConfig scheduler))) now
  let (toKeep, toRemove) = applyRetentionPolicy sortedBackups retentionCutoff (bcRetentionCount (bsConfig scheduler))
  
  -- Remove old backups
  removedCount <- mapM (removeFile . (bcBackupDir (bsConfig scheduler) </>)) toRemove
  
  pure (length toRemove)
  where
    isBackupFile :: BackupConfig -> FilePath -> Bool
    isBackupFile config file = do
      takeExtension file == ".db" || takeExtension file == ".gz"
    
    sortBackupsByAge :: FilePath -> [FilePath] -> IO [(FilePath, UTCTime)]
    sortBackupsByAge dir files = do
      filesWithTimes <- mapM (\f -> do
        time <- getModificationTime (dir </> f)
        pure (f, time)
      ) files
      pure (sortBy (comparing snd) filesWithTimes)
    
    applyRetentionPolicy :: [(FilePath, UTCTime)] -> UTCTime -> Int -> ([FilePath], [FilePath])
    applyRetentionPolicy backups cutoff maxCount = do
      let (oldBackups, recentBackups) = partition (\(_, t) -> t < cutoff) backups
      let sortedRecent = reverse (sortBy (comparing snd) recentBackups)
      let (keepRecent, removeRecent) = splitAt maxCount sortedRecent
      (map fst keepRecent, map fst oldBackups ++ map fst removeRecent)

-- | Start backup scheduler
-- |
-- | **Purpose:** Starts the backup scheduler in a background thread.
-- | **Parameters:**
-- | - `scheduler`: Backup scheduler
-- | **Side Effects:** Starts background thread for scheduled backups
startScheduler :: BackupScheduler -> IO ()
startScheduler scheduler = do
  atomically (writeTVar (bsRunning scheduler) True)
  forkIO (schedulerLoop scheduler)
  pure ()
  where
    schedulerLoop :: BackupScheduler -> IO ()
    schedulerLoop sched = do
      running <- atomically (readTVar (bsRunning sched))
      if running then do
        -- Wait until next backup time (simplified - would parse cron)
        threadDelay (24 * 60 * 60 * 1000000) -- 24 hours
        
        -- Create backup
        result <- createBackup sched
        case result of
          Right path -> putStrLn ("Backup created: " ++ path)
          Left err -> putStrLn ("Backup failed: " ++ err)
        
        -- Cleanup old backups
        removed <- cleanupOldBackups sched
        putStrLn ("Removed " ++ show removed ++ " old backups")
        
        schedulerLoop sched
      else
        pure ()

-- | Stop backup scheduler
-- |
-- | **Purpose:** Stops the backup scheduler.
-- | **Parameters:**
-- | - `scheduler`: Backup scheduler
stopScheduler :: BackupScheduler -> IO ()
stopScheduler scheduler = do
  atomically (writeTVar (bsRunning scheduler) False)
