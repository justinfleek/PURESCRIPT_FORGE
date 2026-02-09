{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Backup Verification & Disaster Recovery - Backup Integrity and Recovery Procedures
-- |
-- | Verifies backup integrity and provides disaster recovery procedures.
module Bridge.Backup.Verification
  ( VerificationResult(..)
  , RestoreResult(..)
  , verifyBackup
  , restoreFromBackup
  , findLatestValidBackup
  , pointInTimeRecovery
  ) where

import Prelude hiding (read)
import Database.SQLite.Simple (Connection, open, close, query_, Only(..))
import qualified Data.Text as T
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import System.Directory (doesFileExist, getModificationTime, copyFile, listDirectory, removeFile, createDirectoryIfMissing)
import System.FilePath ((</>), takeExtension, takeDirectory)
import Data.Time (UTCTime, getCurrentTime)
import Codec.Compression.GZip (decompress)
import Control.Exception (try, SomeException)
import Data.Int (Int64)
import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Maybe (listToMaybe)

-- | Backup verification result
data VerificationResult = VerificationResult
  { vrValid :: Bool
  , vrIntegrityCheck :: T.Text
  , vrFileSize :: Int64
  , vrModifiedTime :: UTCTime
  , vrErrors :: [String]
  } deriving (Eq, Show)

-- | Restore result
data RestoreResult = RestoreResult
  { rrSuccess :: Bool
  , rrBackupPath :: FilePath
  , rrTargetPath :: FilePath
  , rrRestoreTime :: UTCTime
  , rrError :: Maybe String
  } deriving (Eq, Show)

-- | Get file size
getFileSize :: FilePath -> IO Int64
getFileSize path = do
  contents <- BS.readFile path
  pure (fromIntegral (BS.length contents))

-- | Decompress backup file
decompressBackup :: FilePath -> IO FilePath
decompressBackup compressedPath = do
  compressed <- BL.readFile compressedPath
  let decompressed = decompress compressed
  let tempPath = compressedPath ++ ".tmp"
  BL.writeFile tempPath decompressed
  pure tempPath

-- | Check if file is a backup file
isBackupFile :: FilePath -> Bool
isBackupFile f = takeExtension f == ".db" || takeExtension f == ".gz"

-- | List backup files in directory
listBackupFiles :: FilePath -> IO [FilePath]
listBackupFiles dir = do
  files <- listDirectory dir
  pure (filter isBackupFile files)

-- | Verify backup integrity
verifyBackup :: FilePath -> IO (Either String VerificationResult)
verifyBackup backupPath = do
  exists <- doesFileExist backupPath
  if not exists
    then pure (Left ("Backup file not found: " ++ backupPath))
    else do
      result <- try $ do
        -- Get file metadata
        fileSize <- getFileSize backupPath
        modifiedTime <- getModificationTime backupPath
        
        -- Decompress if needed
        dbPath <- if takeExtension backupPath == ".gz"
          then decompressBackup backupPath
          else pure backupPath
        
        -- Open backup database and run integrity check
        conn <- open dbPath
        [Only integrityResult] <- query_ conn "PRAGMA integrity_check" :: IO [Only T.Text]
        [Only quickCheck] <- query_ conn "PRAGMA quick_check" :: IO [Only T.Text]
        close conn
        
        -- Clean up temporary file if decompressed
        if takeExtension backupPath == ".gz"
          then removeFile dbPath
          else pure ()
        
        let isValid = integrityResult == "ok" && quickCheck == "ok"
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
        Left (err :: SomeException) -> pure (Left ("Verification failed: " ++ show err))

-- | Restore from backup
restoreFromBackup :: FilePath -> FilePath -> IO (Either String RestoreResult)
restoreFromBackup backupPath targetPath = do
  startTime <- getCurrentTime
  
  -- Verify backup first
  verification <- verifyBackup backupPath
  case verification of
    Left err -> pure (Left ("Backup verification failed: " ++ err))
    Right vr -> 
      if not (vrValid vr)
        then pure (Left ("Backup is invalid: " ++ show (vrErrors vr)))
        else do
          -- Decompress if needed
          dbPathResult <- if takeExtension backupPath == ".gz"
            then do
              result <- try $ decompressBackup backupPath
              case result of
                Left (err :: SomeException) -> pure (Left ("Decompress failed: " ++ show err))
                Right path -> pure (Right path)
            else pure (Right backupPath)
          
          case dbPathResult of
            Left err -> pure (Left err)
            Right dbPath -> do
              -- Restore backup
              restoreResult <- try $ restoreDatabase dbPath targetPath
              case restoreResult of
                Left (err :: SomeException) -> pure (Left ("Restore database failed: " ++ show err))
                Right _ -> do
                  -- Clean up temporary file if decompressed
                  if takeExtension backupPath == ".gz"
                    then do
                      _ <- try $ removeFile dbPath :: IO (Either SomeException ())
                      pure ()
                    else pure ()
                  
                  -- Verify restored database
                  restoredVerification <- verifyBackup targetPath
                  case restoredVerification of
                    Left err -> pure (Left ("Restored database verification failed: " ++ err))
                    Right vr' ->
                      if not (vrValid vr')
                        then pure (Left ("Restored database is invalid: " ++ show (vrErrors vr')))
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
    restoreDatabase :: FilePath -> FilePath -> IO ()
    restoreDatabase sourcePath destPath = do
      createDirectoryIfMissing True (takeDirectory destPath)
      copyFile sourcePath destPath

-- | Find latest valid backup
findLatestValidBackup :: FilePath -> IO (Either String FilePath)
findLatestValidBackup backupDir = do
  result <- try $ do
    backupFiles <- listBackupFiles backupDir
    sortedBackups <- sortBackupsByTime backupFiles
    findValidBackup sortedBackups
  
  case result of
    Right (Right path) -> pure (Right path)
    Right (Left err) -> pure (Left err)
    Left (err :: SomeException) -> pure (Left ("Failed to find valid backup: " ++ show err))
  where
    sortBackupsByTime :: [FilePath] -> IO [(FilePath, UTCTime)]
    sortBackupsByTime files = do
      filesWithTimes <- mapM (\f -> do
        time <- getModificationTime (backupDir </> f)
        pure (f, time)) files
      pure (reverse (sortBy (comparing snd) filesWithTimes))
    
    findValidBackup :: [(FilePath, UTCTime)] -> IO (Either String FilePath)
    findValidBackup [] = pure (Left "No backups found")
    findValidBackup ((file, _):rest) = do
      verification <- verifyBackup (backupDir </> file)
      case verification of
        Right vr ->
          if vrValid vr
            then pure (Right file)
            else findValidBackup rest
        Left _ -> findValidBackup rest

-- | Point-in-time recovery
pointInTimeRecovery :: FilePath -> UTCTime -> FilePath -> IO (Either String RestoreResult)
pointInTimeRecovery backupDir targetTime targetPath = do
  result <- try $ do
    backupFiles <- listBackupFiles backupDir
    backupsWithTimes <- mapM (\f -> do
      time <- getModificationTime (backupDir </> f)
      pure (f, time)) backupFiles
    
    let validBackups = reverse (sortBy (comparing snd) (filter (\(_, t) -> t <= targetTime) backupsWithTimes))
    
    case listToMaybe validBackups of
      Nothing -> pure (Left ("No backups found before target time: " ++ show targetTime))
      Just (backupFile, _) -> restoreFromBackup (backupDir </> backupFile) targetPath
  
  case result of
    Right r -> pure r
    Left (err :: SomeException) -> pure (Left ("Point-in-time recovery failed: " ++ show err))
