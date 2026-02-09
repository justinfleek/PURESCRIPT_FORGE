{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

-- | Backup Scheduler - Automated Database Backup System
-- |
-- | Schedules and executes automated database backups with retention policies.
-- | Creates full backups, verifies integrity, and manages retention.
-- |
-- | Dependencies:
-- | - Database.SQLite.Simple: Database operations
-- | - System.Directory: File operations
-- | - Data.Time: Timestamp management
module Bridge.Backup.Scheduler where

import Prelude hiding (read)
import Control.Concurrent (threadDelay, forkIO)
import Control.Concurrent.STM (TVar, newTVarIO, readTVar, writeTVar, atomically)
import Control.Exception (try, SomeException)
import Database.SQLite.Simple (Connection, open, close, query_, Only(..))
import Database.SQLite.Simple.Backup (backupFromTo)
import qualified Data.Text as T
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString as BS
import System.Directory (createDirectoryIfMissing, listDirectory, removeFile, getModificationTime)
import System.FilePath ((</>), takeExtension)
import Data.Time (UTCTime, getCurrentTime, addUTCTime)
import Data.Time.Format (formatTime, defaultTimeLocale)
import Data.List (sortBy, partition)
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
-- | Process:
-- | 1. Generate backup filename with timestamp
-- | 2. Open source database
-- | 3. Create backup using SQLite .backup command
-- | 4. Compress if configured
-- | 5. Verify backup integrity
createBackup :: BackupScheduler -> IO (Either String FilePath)
createBackup scheduler = do
  result <- try $ do
    now <- getCurrentTime
    let timestamp = formatTime defaultTimeLocale "%Y%m%d_%H%M%S" now
    let backupFile = bcBackupDir (bsConfig scheduler) </> ("backup_" <> timestamp <> ".db")

    -- Open source database
    sourceConn <- open (bsDbPath scheduler)

    -- Create backup via SQLite backup API
    destConn <- open backupFile
    backupFromTo sourceConn "main" destConn "main"
    close destConn

    -- Verify backup
    verifyConn <- open backupFile
    [Only integrityResult] <- query_ verifyConn "PRAGMA integrity_check"
    close verifyConn

    if (integrityResult :: T.Text) /= "ok" then
      pure (Left ("Backup integrity check failed: " <> T.unpack integrityResult))
    else do
      -- Compress if configured
      finalPath <- if bcCompress (bsConfig scheduler) then do
        contents <- BS.readFile backupFile
        let compressed = compress (BL.fromStrict contents)
        let compressedPath = backupFile <> ".gz"
        BL.writeFile compressedPath compressed
        removeFile backupFile
        pure compressedPath
      else
        pure backupFile

      close sourceConn
      pure (Right finalPath)

  case result of
    Right (Right path) -> pure (Right path)
    Right (Left err) -> pure (Left err)
    Left err -> pure (Left ("Backup failed: " ++ show (err :: SomeException)))

-- | Cleanup old backups
-- |
-- | Removes old backups based on retention policy.
-- | Returns number of backups removed.
cleanupOldBackups :: BackupScheduler -> IO Int
cleanupOldBackups scheduler = do
  now <- getCurrentTime
  backupFiles <- listDirectory (bcBackupDir (bsConfig scheduler))
  let validFiles = filter isBackupFile backupFiles

  -- Sort by modification time (oldest first)
  sortedBackups <- sortBackupsByAge (bcBackupDir (bsConfig scheduler)) validFiles

  -- Apply retention policies
  let retentionSeconds = fromIntegral (bcRetentionDays (bsConfig scheduler) * 86400)
  let retentionCutoff = addUTCTime (negate retentionSeconds) now
  let (oldBackups, recentBackups) = partition (\(_, t) -> t < retentionCutoff) sortedBackups
  let sortedRecent = reverse (sortBy (comparing snd) recentBackups)
  let maxCount = bcRetentionCount (bsConfig scheduler)
  let (_keepRecent, removeRecent) = splitAt maxCount sortedRecent
  let toRemove = map fst oldBackups ++ map fst removeRecent

  -- Remove old backups
  mapM_ (\f -> removeFile (bcBackupDir (bsConfig scheduler) </> f)) toRemove

  pure (length toRemove)
  where
    isBackupFile :: FilePath -> Bool
    isBackupFile file = takeExtension file == ".db" || takeExtension file == ".gz"

    sortBackupsByAge :: FilePath -> [FilePath] -> IO [(FilePath, UTCTime)]
    sortBackupsByAge dir files = do
      filesWithTimes <- mapM (\f -> do
        time <- getModificationTime (dir </> f)
        pure (f, time)
        ) files
      pure (sortBy (comparing snd) filesWithTimes)

-- | Start backup scheduler
-- |
-- | Starts the backup scheduler in a background thread.
startScheduler :: BackupScheduler -> IO ()
startScheduler scheduler = do
  atomically (writeTVar (bsRunning scheduler) True)
  _ <- forkIO (schedulerLoop scheduler)
  pure ()
  where
    schedulerLoop :: BackupScheduler -> IO ()
    schedulerLoop sched = do
      running <- atomically (readTVar (bsRunning sched))
      if running then do
        -- Wait until next backup time (simplified - 24 hours)
        threadDelay (24 * 60 * 60 * 1000000)

        -- Create backup
        backupResult <- createBackup sched
        case backupResult of
          Right path -> putStrLn ("Backup created: " ++ path)
          Left err -> putStrLn ("Backup failed: " ++ err)

        -- Cleanup old backups
        removed <- cleanupOldBackups sched
        putStrLn ("Removed " ++ show removed ++ " old backups")

        schedulerLoop sched
      else
        pure ()

-- | Stop backup scheduler
stopScheduler :: BackupScheduler -> IO ()
stopScheduler scheduler = do
  atomically (writeTVar (bsRunning scheduler) False)
