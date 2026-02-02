-- | Database Tests
-- | Property tests for database operations
module Bridge.DatabaseSpec where

import Test.Hspec
import Bridge.Database
import Bridge.Database.Schema
import System.Directory (removeFile, doesFileExist)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Time (getCurrentTime)

-- | Test database operations
spec :: Spec
spec = do
  describe "Database Operations" $ do
    it "opens database successfully" $ do
      -- Test: openDatabase creates valid handle
      handle <- openDatabase ":memory:"
      -- Handle should be created (no exception)
      pure ()
    
    it "saves and retrieves snapshot correctly" $ do
      -- Test: saveSnapshot preserves data integrity
      handle <- openDatabase ":memory:"
      now <- getCurrentTime
      
      let snapshotId = T.pack "test-snapshot-1"
      let stateHash = T.pack "abc123"
      let stateData = T.pack """{"balance":{"venice":{"diem":1000.0}}}"""
      let trigger = Just (T.pack "manual")
      let description = Just (T.pack "Test snapshot")
      
      -- Save snapshot
      savedId <- saveSnapshotFFI handle snapshotId (T.pack (show now)) stateHash stateData trigger description
      savedId `shouldBe` snapshotId
      
      -- Retrieve snapshot
      retrieved <- getSnapshotFFI handle snapshotId
      retrieved `shouldSatisfy` isJust
      
      -- Verify data
      case retrieved of
        Just snap -> do
          snapshotId snap `shouldBe` snapshotId
          snapshotStateHash snap `shouldBe` stateHash
          snapshotData snap `shouldBe` stateData
        Nothing -> expectationFailure "Snapshot should exist"
    
    it "saves and retrieves session correctly" $ do
      -- Test: saveSession preserves session data
      handle <- openDatabase ":memory:"
      now <- getCurrentTime
      
      let recordId = T.pack "test-record-1"
      let sessionId = T.pack "test-session-1"
      let timestamp = T.pack (show now)
      
      -- Save session
      savedId <- saveSessionFFI handle recordId sessionId 100 200 300 0.05 (T.pack "claude-3-opus") (T.pack "venice") timestamp Nothing
      savedId `shouldBe` recordId
      
      -- Retrieve sessions
      sessions <- getSessionsBySessionIdFFI handle sessionId
      length sessions `shouldSatisfy` (>= 1)
      
      -- Verify data
      case sessions of
        (session:_) -> do
          sessionRecordSessionId session `shouldBe` sessionId
          sessionRecordPromptTokens session `shouldBe` 100
          sessionRecordCompletionTokens session `shouldBe` 200
          sessionRecordTotalTokens session `shouldBe` 300
          sessionRecordCost session `shouldBe` 0.05
        [] -> expectationFailure "Session should exist"
    
    it "records and retrieves balance history correctly" $ do
      -- Test: recordBalanceHistory preserves balance data
      handle <- openDatabase ":memory:"
      
      -- Record balance
      recordId <- recordBalanceHistoryFFI handle 1000.0 50.0 1050.0 10.0 (Just 100)
      recordId `shouldSatisfy` (not . T.null)
      
      -- Retrieve balance history
      history <- getBalanceHistoryFFI handle (Just 10) (Just 0)
      length history `shouldSatisfy` (>= 1)
      
      -- Verify data
      case history of
        (record:_) -> do
          balanceHistoryDiem record `shouldBe` 1000.0
          balanceHistoryUsd record `shouldBe` 50.0
          balanceHistoryEffective record `shouldBe` 1050.0
          balanceHistoryConsumptionRate record `shouldBe` 10.0
        [] -> expectationFailure "Balance record should exist"

-- | Test database invariants
testInvariants :: Spec
testInvariants = do
  describe "Database Invariants" $ do
    it "snapshot IDs are unique" $ do
      -- Property: No duplicate snapshot IDs
      handle <- openDatabase ":memory:"
      now <- getCurrentTime
      
      let snapshotId = T.pack "unique-snapshot"
      let stateHash = T.pack "hash1"
      let stateData = T.pack """{"test":1}"""
      let timestamp = T.pack (show now)
      
      -- Save first snapshot
      _ <- saveSnapshotFFI handle snapshotId timestamp stateHash stateData (Just (T.pack "manual")) Nothing
      
      -- Try to save duplicate (should overwrite)
      _ <- saveSnapshotFFI handle snapshotId timestamp stateHash stateData (Just (T.pack "manual")) Nothing
      
      -- Should only have one snapshot
      snapshots <- listSnapshotsFFI handle (Just 10) (Just 0)
      length snapshots `shouldBe` 1
    
    it "balance history is ordered by timestamp" $ do
      -- Property: Balance history entries are chronologically ordered
      handle <- openDatabase ":memory:"
      
      -- Record multiple balances
      _ <- recordBalanceHistoryFFI handle 1000.0 50.0 1050.0 10.0 (Just 100)
      _ <- recordBalanceHistoryFFI handle 950.0 50.0 1000.0 10.0 (Just 90)
      _ <- recordBalanceHistoryFFI handle 900.0 50.0 950.0 10.0 (Just 80)
      
      -- Retrieve history
      history <- getBalanceHistoryFFI handle (Just 10) (Just 0)
      length history `shouldSatisfy` (>= 3)
      
      -- Verify ordering (descending by timestamp)
      let timestamps = map balanceHistoryTimestamp history
      timestamps `shouldSatisfy` isDescending
      
      where
        isDescending [] = True
        isDescending [_] = True
        isDescending (x:y:xs) = x >= y && isDescending (y:xs)
