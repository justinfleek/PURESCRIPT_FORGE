{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ScopedTypeVariables #-}

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

import Prelude hiding (read)
import Database.SQLite.Simple (open, close, query_, Only(..))
import qualified Data.Text as T
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import System.Directory (doesFileExist, getModificationTime, copyFile, listDirectory, removeFile, createDirectoryIfMissing)
import System.FilePath ((</>), takeExtension, takeDirectory)
import Data.Time (UTCTime, getCurrentTime)
import Codec.Compression.GZip (decompress)
import Control.Exception (try, SomeException)
import Data.Int (Int64)
import Data.List (sortBy, partition)
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
      dbPath <- if takeExtension backupPath == ".gz" then
        decompressBackupFile backupPath
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
        pure ()
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
    getFileSize :: FilePath -> IO Int64
    getFileSize path = do
      contents <- BS.readFile path
      pure (fromIntegral (BS.length contents))
    
    decompressBackupFile :: FilePath -> IO FilePath
    decompressBackupFile compressedPath = do
      compressed <- BL.readFile compressedPath
      let decompressed = decompress compressed
      let tempPath = compressedPath ++ ".tmp"
      BL.writeFile tempPath decompressed
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
  -- Verify backup first
  verification <- verifyBackup backupPath
  case verification of
    Left err -> pure (Left ("Backup verification failed: " ++ err))
    Right vr -> if not (vrValid vr) then
      pure (Left ("Backup is invalid: " ++ show (vrErrors vr)))
    else do
      -- Decompress if needed
      dbPathResult <- if takeExtension backupPath == ".gz" then do
        decompressResult <- try $ decompressBackupFile backupPath
        case decompressResult of
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
                cleanupResult <- try $ removeFile dbPath
                case cleanupResult of
                  Left (_ :: SomeException) -> pure () -- Ignore cleanup errors
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
    decompressBackupFile :: FilePath -> IO FilePath
    decompressBackupFile compressedPath = do
      compressed <- BL.readFile compressedPath
      let decompressed = decompress compressed
      let tempPath = compressedPath ++ ".tmp"
      BL.writeFile tempPath decompressed
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
    files <- listDirectory backupDir
    let backupFiles = filter isBackupFile files
    
    -- Sort by modification time (newest first)
    sortedBackups <- sortBackupsByTime backupDir backupFiles
    
    -- Find first valid backup
    findValidBackup backupDir sortedBackups
  
  case result of
    Right (Right path) -> pure (Right path)
    Right (Left err) -> pure (Left err)
    Left err -> pure (Left ("Failed to find valid backup: " ++ show (err :: SomeException)))
  where
    isBackupFile :: FilePath -> Bool
    isBackupFile f = takeExtension f == ".db" || takeExtension f == ".gz"
    
    sortBackupsByTime :: FilePath -> [FilePath] -> IO [(FilePath, UTCTime)]
    sortBackupsByTime dir files = do
      filesWithTimes <- mapM (getFileWithTime dir) files
      pure (reverse (sortBy (comparing snd) filesWithTimes))
    
    getFileWithTime :: FilePath -> FilePath -> IO (FilePath, UTCTime)
    getFileWithTime dir f = do
      time <- getModificationTime (dir </> f)
      pure (f, time)
    
    findValidBackup :: FilePath -> [(FilePath, UTCTime)] -> IO (Either String FilePath)
    findValidBackup _ [] = pure (Left "No backups found")
    findValidBackup dir ((file, _):rest) = do
      verificationResult <- verifyBackup (dir </> file)
      case verificationResult of
        Right vr -> if vrValid vr then
          pure (Right file)
        else
          findValidBackup dir rest
        Left _ -> findValidBackup dir rest

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
    files <- listDirectory backupDir
    let backupFiles = filter isBackupFile files
    backupsWithTimes <- mapM (getFileWithTime backupDir) backupFiles
    
    -- Filter backups before target time and sort
    let validBackups = reverse (sortBy (comparing snd) (filter (\(_, t) -> t <= targetTime) backupsWithTimes))
    
    case validBackups of
      [] -> pure (Left ("No backups found before target time: " ++ show targetTime))
      (backupFile, _):_ -> do
        -- Restore from backup
        restoreFromBackup (backupDir </> backupFile) targetPath
  
  case result of
    Right restoreResult -> pure restoreResult
    Left err -> pure (Left ("Point-in-time recovery failed: " ++ show (err :: SomeException)))
  where
    isBackupFile :: FilePath -> Bool
    isBackupFile f = takeExtension f == ".db" || takeExtension f == ".gz"
    
    getFileWithTime :: FilePath -> FilePath -> IO (FilePath, UTCTime)
    getFileWithTime dir f = do
      time <- getModificationTime (dir </> f)
      pure (f, time)
