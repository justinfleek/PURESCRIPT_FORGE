{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

-- | Backup Verification & Disaster Recovery - Backup Integrity and Recovery Procedures
-- |
-- | **What:** Verifies backup integrity and provides disaster recovery procedures.
-- |         Validates backups, tests restore procedures, and manages recovery workflows.
-- | **Why:** Ensures backups are valid and can be restored. Enables rapid recovery
-- |         from disasters. Prevents silent backup corruption.
-- | **How:** Verifies backups using SQLite integrity checks, tests restore procedures,
-- |         and provides point-in-time recovery workflows.
-- |
-- | **Dependencies:**
-- | - `Database.SQLite.Simple`: Database operations
-- | - `Bridge.Backup.Scheduler`: Backup management
-- |
-- | **Mathematical Foundation:**
-- | - **Integrity Check:** `PRAGMA integrity_check` returns "ok" iff backup valid
-- | - **Recovery Point:** Latest valid backup before corruption timestamp
-- | - **Recovery Time:** Time to restore from backup
-- |
-- | **Usage Example:**
-- | ```haskell
-- | import Bridge.Backup.Verification as Verification
-- |
-- | -- Verify backup
-- | result <- Verification.verifyBackup backupPath
-- | case result of
-- |   Right _ -> -- Backup valid
-- |   Left err -> -- Backup invalid
-- |
-- | -- Restore from backup
-- | restoreResult <- Verification.restoreFromBackup backupPath targetPath
-- | ```
module Bridge.Backup.Verification where

module Bridge.Backup.Verification where

import Prelude hiding (read)
import Database.SQLite.Simple (Connection, open, close, query_, Only(..))
import Database.SQLite.Simple.Backup (backupFromTo)
import qualified Data.Text as T
import qualified Data.ByteString as BS
import System.Directory (doesFileExist, getModificationTime, copyFile, listDirectory, removeFile, createDirectoryIfMissing)
import System.FilePath ((</>), takeExtension, takeDirectory)
import Data.Time (UTCTime, getCurrentTime)
import Codec.Compression.GZip (decompress)
import Control.Exception (try, SomeException)
import Data.Int (Int64)
import Data.List (sortBy, filter, reverse, null, head, partition, splitAt)
import Data.Ord (comparing)

-- | Backup verification result
data VerificationResult = VerificationResult
  { vrValid :: Bool
  , vrIntegrityCheck :: T.Text
  , vrFileSize :: Int64
  , vrModifiedTime :: UTCTime
  , vrErrors :: [String]
  }
  deriving (Eq, Show)

-- | Restore result
data RestoreResult = RestoreResult
  { rrSuccess :: Bool
  , rrBackupPath :: FilePath
  , rrTargetPath :: FilePath
  , rrRestoreTime :: UTCTime
  , rrError :: Maybe String
  }
  deriving (Eq, Show)

-- | Verify backup integrity
-- |
-- | **Purpose:** Verifies backup file integrity using SQLite integrity checks.
-- | **Parameters:**
-- | - `backupPath`: Path to backup file
-- | **Returns:** Either error or verification result
-- |
-- | **Process:**
-- | 1. Check if file exists
-- | 2. Decompress if needed
-- | 3. Open backup database
-- | 4. Run integrity check
-- | 5. Return verification result
verifyBackup :: FilePath -> IO (Either String VerificationResult)
verifyBackup backupPath = do
  -- Check if file exists
  exists <- doesFileExist backupPath
  if not exists then
    pure (Left ("Backup file not found: " ++ backupPath))
  else do
    result <- try $ do
    
    -- Get file metadata
    fileSize <- getFileSize backupPath
    modifiedTime <- getModificationTime backupPath
    
    -- Decompress if needed
    dbPath <- if takeExtension backupPath == ".gz" then do
      decompressBackup backupPath
    else
      pure backupPath
    
    -- Open backup database
    conn <- open dbPath
    
    -- Run integrity check
    [Only integrityResult] <- query_ conn "PRAGMA integrity_check"
    
    -- Run quick check
    [Only quickCheck] <- query_ conn "PRAGMA quick_check"
    
    close conn
    
    -- Clean up temporary file if decompressed
    if takeExtension backupPath == ".gz" then do
      removeFile dbPath
    else
      pure ()
    
    let isValid = integrityResult == ("ok" :: T.Text) && quickCheck == ("ok" :: T.Text)
    let errors = if isValid then [] else [T.unpack integrityResult, T.unpack quickCheck]
    
    pure VerificationResult
      { vrValid = isValid
      , vrIntegrityCheck = integrityResult
      , vrFileSize = fileSize
      , vrModifiedTime = modifiedTime
      , vrErrors = errors
      }
  
  case result of
    Right value -> pure (Right value)
    Left err -> pure (Left ("Verification failed: " ++ show (err :: SomeException)))
  where
    import System.Directory (removeFile)
    import Data.Int (Int64)
    
    getFileSize :: FilePath -> IO Int64
    getFileSize path = do
      contents <- BS.readFile path
      pure (fromIntegral (BS.length contents))
    
    decompressBackup :: FilePath -> IO FilePath
    decompressBackup compressedPath = do
      compressed <- BS.readFile compressedPath
      let decompressed = decompress compressed
      let tempPath = compressedPath ++ ".tmp"
      BS.writeFile tempPath decompressed
      pure tempPath

-- | Restore from backup
-- |
-- | **Purpose:** Restores database from backup file.
-- | **Parameters:**
-- | - `backupPath`: Path to backup file
-- | - `targetPath`: Path to restore database to
-- | **Returns:** Either error or restore result
-- |
-- | **Process:**
-- | 1. Verify backup integrity
-- | 2. Decompress if needed
-- | 3. Copy backup to target location
-- | 4. Verify restored database
restoreFromBackup :: FilePath -> FilePath -> IO (Either String RestoreResult)
restoreFromBackup backupPath targetPath = do
  startTime <- getCurrentTime
  
  -- Verify backup first
  verification <- verifyBackup backupPath
  case verification of
    Left err -> pure (Left ("Backup verification failed: " ++ err))
    Right vr -> if not (vrValid vr) then
      pure (Left ("Backup is invalid: " ++ show (vrErrors vr)))
    else do
      -- Decompress if needed
      dbPathResult <- if takeExtension backupPath == ".gz" then do
        result <- try $ decompressBackup backupPath
        case result of
          Left err -> pure (Left ("Decompress failed: " ++ show (err :: SomeException)))
          Right path -> pure (Right path)
      else
        pure (Right backupPath)
      
      case dbPathResult of
        Left err -> pure (Left err)
        Right dbPath -> do
          -- Restore backup
          restoreResult <- try $ restoreDatabase dbPath targetPath
          case restoreResult of
            Left err -> pure (Left ("Restore database failed: " ++ show (err :: SomeException)))
            Right _ -> do
              -- Clean up temporary file if decompressed
              if takeExtension backupPath == ".gz" then do
                removeResult <- try $ removeFile dbPath
                case removeResult of
                  Left _ -> pure () -- Ignore cleanup errors
                  Right _ -> pure ()
              else
                pure ()
              
              -- Verify restored database
              restoredVerification <- verifyBackup targetPath
              case restoredVerification of
                Left err -> pure (Left ("Restored database verification failed: " ++ err))
                Right vr' -> if not (vrValid vr') then
                  pure (Left ("Restored database is invalid: " ++ show (vrErrors vr')))
                else do
                  endTime <- getCurrentTime
                  pure (Right RestoreResult
                    { rrSuccess = True
                    , rrBackupPath = backupPath
                    , rrTargetPath = targetPath
                    , rrRestoreTime = endTime
                    , rrError = Nothing
                    })
  where
    import System.Directory (removeFile, createDirectoryIfMissing)
    import System.FilePath (takeDirectory)
    
    decompressBackup :: FilePath -> IO FilePath
    decompressBackup compressedPath = do
      compressed <- BS.readFile compressedPath
      let decompressed = decompress compressed
      let tempPath = compressedPath ++ ".tmp"
      BS.writeFile tempPath decompressed
      pure tempPath
    
    restoreDatabase :: FilePath -> FilePath -> IO ()
    restoreDatabase sourcePath destPath = do
      -- Create destination directory if needed
      createDirectoryIfMissing True (takeDirectory destPath)
      
      -- Copy backup to target
      copyFile sourcePath destPath

-- | Find latest valid backup
-- |
-- | **Purpose:** Finds the latest valid backup in backup directory.
-- | **Parameters:**
-- | - `backupDir`: Backup directory path
-- | **Returns:** Either error or backup file path
findLatestValidBackup :: FilePath -> IO (Either String FilePath)
findLatestValidBackup backupDir = do
  result <- try $ do
    -- List backup files
    backupFiles <- listBackupFiles backupDir
    
    -- Sort by modification time (newest first)
    sortedBackups <- sortBackupsByTime backupFiles
    
    -- Find first valid backup
    findValidBackup sortedBackups
  where
    import System.Directory (listDirectory)
    import Data.List (sortBy)
    import Data.Ord (comparing)
    
    listBackupFiles :: FilePath -> IO [FilePath]
    listBackupFiles dir = do
      files <- listDirectory dir
      pure (filter isBackupFile files)
      where
        isBackupFile :: FilePath -> Bool
        isBackupFile f = takeExtension f == ".db" || takeExtension f == ".gz"
    
    sortBackupsByTime :: [FilePath] -> IO [(FilePath, UTCTime)]
    sortBackupsByTime files = do
      filesWithTimes <- mapM (\f -> do
        time <- getModificationTime (backupDir </> f)
        pure (f, time)
      ) files
      pure (reverse (sortBy (comparing snd) filesWithTimes))
    
    findValidBackup :: [(FilePath, UTCTime)] -> IO (Either String FilePath)
    findValidBackup [] = pure (Left "No backups found")
    findValidBackup ((file, _):rest) = do
      verification <- verifyBackup (backupDir </> file)
      case verification of
        Right vr -> if vrValid vr then
          pure (Right file)
        else
          findValidBackup rest
        Left _ -> findValidBackup rest
  
  case result of
    Right (Right path) -> pure (Right path)
    Right (Left err) -> pure (Left err)
    Left err -> pure (Left ("Failed to find valid backup: " ++ show (err :: SomeException)))

-- | Point-in-time recovery
-- |
-- | **Purpose:** Restores database to a specific point in time using backups.
-- | **Parameters:**
-- | - `backupDir`: Backup directory
-- | - `targetTime`: Target recovery time
-- | - `targetPath`: Path to restore database to
-- | **Returns:** Either error or restore result
pointInTimeRecovery :: FilePath -> UTCTime -> FilePath -> IO (Either String RestoreResult)
pointInTimeRecovery backupDir targetTime targetPath = do
  result <- try $ do
    -- Find backup closest to target time (before target time)
    backupFiles <- listBackupFiles backupDir
    backupsWithTimes <- mapM (\f -> do
      time <- getModificationTime (backupDir </> f)
      pure (f, time)
    ) backupFiles
    
    -- Filter backups before target time and sort
    let validBackups = reverse (sortBy (comparing snd) (filter (\(_, t) -> t <= targetTime) backupsWithTimes))
    
    case validBackups of
      [] -> pure (Left ("No backups found before target time: " ++ show targetTime))
      (backupFile, _):_ -> do
        -- Restore from backup
        restoreFromBackup (backupDir </> backupFile) targetPath
  where
    import System.Directory (listDirectory, getModificationTime)
    import Data.List (sortBy, filter, reverse, null, head)
    import Data.Ord (comparing)
    
    listBackupFiles :: FilePath -> IO [FilePath]
    listBackupFiles dir = do
      files <- listDirectory dir
      pure (filter isBackupFile files)
      where
        isBackupFile :: FilePath -> Bool
        isBackupFile f = takeExtension f == ".db" || takeExtension f == ".gz"
