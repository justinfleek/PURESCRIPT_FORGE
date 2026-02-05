{-# LANGUAGE OverloadedStrings #-}

-- | Backup Integration Tests - End-to-End Backup and Recovery Flow Tests
-- |
-- | **What:** Integration tests for backup and recovery workflows. Tests complete
-- |         backup creation, verification, and restore procedures.
-- | **Why:** Ensures backup system works correctly end-to-end. Validates disaster
-- |         recovery procedures.
-- | **How:** Creates test database, performs backups, verifies integrity, tests restore.
module Bridge.Integration.BackupSpec where

import Test.Hspec
import Test.QuickCheck
import Bridge.Backup.Scheduler
import Bridge.Backup.Verification
import Database.SQLite.Simple
import System.Directory (removeFile, doesFileExist)
import System.FilePath ((</>))
import qualified Data.Text as T

-- | Test backup creation and verification flow
testBackupCreationAndVerification :: Spec
testBackupCreationAndVerification = describe "Backup Creation and Verification" $ do
  it "creates backup and verifies integrity" $ do
    -- Create test database
    testDbPath <- createTestDatabase
    
    -- Create backup scheduler
    config <- pure defaultBackupConfig { bcBackupDir = "./test-backups" }
    scheduler <- createScheduler config testDbPath
    
    -- Create backup
    backupResult <- createBackup scheduler
    case backupResult of
      Right backupPath -> do
        -- Verify backup
        verificationResult <- verifyBackup backupPath
        case verificationResult of
          Right vr -> do
            vrValid vr `shouldBe` True
            vrIntegrityCheck vr `shouldBe` ("ok" :: T.Text)
          Left err -> expectationFailure ("Backup verification failed: " ++ err)
      Left err -> expectationFailure ("Backup creation failed: " ++ err)
    
    -- Cleanup
    cleanupTestDatabase testDbPath
  where
    createTestDatabase :: IO FilePath
    createTestDatabase = do
      let dbPath = "./test-db-integration.db"
      conn <- open dbPath
      execute_ conn "CREATE TABLE IF NOT EXISTS test_table (id INTEGER PRIMARY KEY, value TEXT)"
      execute conn "INSERT INTO test_table (value) VALUES (?)" (Only ("test-value" :: T.Text))
      close conn
      pure dbPath
    
    cleanupTestDatabase :: FilePath -> IO ()
    cleanupTestDatabase dbPath = do
      exists <- doesFileExist dbPath
      if exists then removeFile dbPath else pure ()

-- | Test restore from backup flow
testRestoreFromBackup :: Spec
testRestoreFromBackup = describe "Restore From Backup" $ do
  it "restores database from backup" $ do
    -- Create test database and backup
    testDbPath <- createTestDatabase
    config <- pure defaultBackupConfig { bcBackupDir = "./test-backups" }
    scheduler <- createScheduler config testDbPath
    
    backupResult <- createBackup scheduler
    case backupResult of
      Right backupPath -> do
        -- Restore to new location
        restorePath <- pure "./test-restored.db"
        restoreResult <- restoreFromBackup backupPath restorePath
        
        case restoreResult of
          Right rr -> do
            rrSuccess rr `shouldBe` True
            
            -- Verify restored database
            conn <- open restorePath
            [Only value] <- query_ conn "SELECT value FROM test_table LIMIT 1"
            close conn
            value `shouldBe` ("test-value" :: T.Text)
            
            -- Cleanup
            removeFile restorePath
          Left err -> expectationFailure ("Restore failed: " ++ err)
      Left err -> expectationFailure ("Backup creation failed: " ++ err)
    
    cleanupTestDatabase testDbPath
  where
    createTestDatabase :: IO FilePath
    createTestDatabase = do
      let dbPath = "./test-db-restore.db"
      conn <- open dbPath
      execute_ conn "CREATE TABLE IF NOT EXISTS test_table (id INTEGER PRIMARY KEY, value TEXT)"
      execute conn "INSERT INTO test_table (value) VALUES (?)" (Only ("test-value" :: T.Text))
      close conn
      pure dbPath
    
    cleanupTestDatabase :: FilePath -> IO ()
    cleanupTestDatabase dbPath = do
      exists <- doesFileExist dbPath
      if exists then removeFile dbPath else pure ()

-- | Test point-in-time recovery flow
testPointInTimeRecovery :: Spec
testPointInTimeRecovery = describe "Point-in-Time Recovery" $ do
  it "recovers database to specific point in time" $ do
    -- Create test database
    testDbPath <- createTestDatabase
    config <- pure defaultBackupConfig { bcBackupDir = "./test-backups" }
    scheduler <- createScheduler config testDbPath
    
    -- Create backup
    backupResult <- createBackup scheduler
    case backupResult of
      Right backupPath -> do
        -- Get backup timestamp
        backupTime <- getModificationTime backupPath
        
        -- Restore to point in time
        restorePath <- pure "./test-pitr.db"
        recoveryResult <- pointInTimeRecovery "./test-backups" backupTime restorePath
        
        case recoveryResult of
          Right rr -> do
            rrSuccess rr `shouldBe` True
            
            -- Verify restored database
            conn <- open restorePath
            [Only value] <- query_ conn "SELECT value FROM test_table LIMIT 1"
            close conn
            value `shouldBe` ("test-value" :: T.Text)
            
            -- Cleanup
            removeFile restorePath
          Left err -> expectationFailure ("Point-in-time recovery failed: " ++ err)
      Left err -> expectationFailure ("Backup creation failed: " ++ err)
    
    cleanupTestDatabase testDbPath
  where
    import System.Directory (getModificationTime)
    
    createTestDatabase :: IO FilePath
    createTestDatabase = do
      let dbPath = "./test-db-pitr.db"
      conn <- open dbPath
      execute_ conn "CREATE TABLE IF NOT EXISTS test_table (id INTEGER PRIMARY KEY, value TEXT)"
      execute conn "INSERT INTO test_table (value) VALUES (?)" (Only ("test-value" :: T.Text))
      close conn
      pure dbPath
    
    cleanupTestDatabase :: FilePath -> IO ()
    cleanupTestDatabase dbPath = do
      exists <- doesFileExist dbPath
      if exists then removeFile dbPath else pure ()

-- | Integration test suite
spec :: Spec
spec = do
  testBackupCreationAndVerification
  testRestoreFromBackup
  testPointInTimeRecovery
