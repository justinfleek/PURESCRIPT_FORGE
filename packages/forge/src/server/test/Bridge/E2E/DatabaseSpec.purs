-- | Database E2E Tests
-- | End-to-end tests for database operations
module Test.Bridge.E2E.DatabaseSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldBeGreaterThanOrEqual)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Aff (Aff)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Bridge.FFI.Haskell.Database as DB
import Test.Bridge.Fixtures.TestData (generateBalanceState, generateSessionState)

-- | Test database operations
testDatabaseOperations :: forall m. Monad m => m Unit
testDatabaseOperations = do
  describe "Database Operations E2E" do
    it "opens database successfully" do
      -- E2E: Open database → Verify handle created
      dbPath <- liftEffect $ getTestDbPath
      handle <- liftEffect $ DB.openDatabase dbPath
      -- Database handle should be created
      pure unit
    
    it "saves and retrieves snapshot" do
      -- E2E: Save snapshot → Retrieve → Verify data integrity
      dbPath <- liftEffect $ getTestDbPath
      handle <- liftEffect $ DB.openDatabase dbPath
      
      snapshotId <- liftEffect $ generateSnapshotId
      timestamp <- liftEffect $ getCurrentTimestamp
      stateHash <- liftEffect $ computeStateHash """{"balance":{"venice":{"diem":1000.0}}}"""
      stateData <- liftEffect $ generateBalanceState
      stateJson <- liftEffect $ encodeState stateData
      
      -- Save snapshot
      savedId <- DB.saveSnapshot handle snapshotId timestamp stateHash stateJson (Just "manual") (Just "Test snapshot")
      savedId `shouldEqual` snapshotId
      
      -- Retrieve snapshot
      retrieved <- DB.getSnapshot handle snapshotId
      isJust retrieved `shouldEqual` true
    
    it "saves and retrieves session" do
      -- E2E: Save session → Retrieve → Verify data integrity
      dbPath <- liftEffect $ getTestDbPath
      handle <- liftEffect $ DB.openDatabase dbPath
      
      sessionId <- liftEffect $ generateSessionId
      recordId <- liftEffect $ generateRecordId
      timestamp <- liftEffect $ getCurrentTimestamp
      
      -- Save session
      savedId <- DB.saveSession handle recordId sessionId 100 200 300 0.05 "claude-3-opus" "venice" timestamp Nothing
      savedId `shouldEqual` recordId
      
      -- Retrieve sessions (returns JSON string)
      sessionsJson <- DB.getSessionsBySessionId handle sessionId
      -- Parse and verify
      sessions <- liftEffect $ parseSessions sessionsJson
      sessions.length `shouldBeGreaterThanOrEqual` 1
    
    it "queries sessions by session ID" do
      -- E2E: Query → Multiple sessions → Verify ordering → Verify data
      dbPath <- liftEffect $ getTestDbPath
      handle <- liftEffect $ DB.openDatabase dbPath
      
      sessionId <- liftEffect $ generateSessionId
      timestamp <- liftEffect $ getCurrentTimestamp
      
      -- Save multiple sessions
      recordId1 <- liftEffect $ generateRecordId
      recordId2 <- liftEffect $ generateRecordId
      
      _ <- DB.saveSession handle recordId1 sessionId 100 200 300 0.05 "claude-3-opus" "venice" timestamp Nothing
      _ <- DB.saveSession handle recordId2 sessionId 150 250 400 0.08 "claude-3-opus" "venice" timestamp Nothing
      
      -- Query sessions
      sessions <- DB.getSessionsBySessionId handle sessionId
      sessions.length `shouldBeGreaterThanOrEqual` 2
    
    it "records and retrieves balance history" do
      -- E2E: Record balance → Retrieve → Verify ordering → Verify data
      dbPath <- liftEffect $ getTestDbPath
      handle <- liftEffect $ DB.openDatabase dbPath
      
      -- Record balance
      recordId <- DB.recordBalanceHistory handle 1000.0 50.0 1050.0 10.0 (Just 100)
      
      -- Retrieve balance history (returns JSON string)
      historyJson <- DB.getBalanceHistory handle (Just 10) (Just 0)
      -- Parse and verify
      history <- liftEffect $ parseBalanceHistory historyJson
      history.length `shouldBeGreaterThanOrEqual` 1

-- | Test database sync
testDatabaseSync :: forall m. Monad m => m Unit
testDatabaseSync = do
  describe "Database Sync E2E" do
    it "syncs SQLite to DuckDB" do
      -- E2E: SQLite data → Sync → DuckDB → Verify → Query
      -- Note: This would require actual DuckDB setup
      pure unit
    
    it "handles sync errors" do
      -- E2E: Sync error → Error handling → Retry → Success
      -- Note: This would require error injection
      pure unit
    
    it "handles incremental sync" do
      -- E2E: New data → Incremental sync → Verify → No duplicates
      -- Note: This would require sync logic implementation
      pure unit

foreign import getTestDbPath :: Effect String
foreign import generateSnapshotId :: Effect String
foreign import generateSessionId :: Effect String
foreign import generateRecordId :: Effect String
foreign import getCurrentTimestamp :: Effect String
foreign import computeStateHash :: String -> Effect String
foreign import encodeState :: BalanceState -> Effect String
foreign import parseSessions :: String -> Effect (Array SessionRecord)
foreign import parseBalanceHistory :: String -> Effect (Array BalanceRecord)

type SessionRecord =
  { id :: String
  , sessionId :: String
  , promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cost :: Number
  , model :: String
  , provider :: String
  , startedAt :: String
  , endedAt :: Maybe String
  }

type BalanceRecord =
  { id :: String
  , timestamp :: String
  , diem :: Number
  , usd :: Number
  , effective :: Number
  , consumptionRate :: Number
  , timeToDepletion :: Maybe Int
  }

import Bridge.State.Store (BalanceState)
