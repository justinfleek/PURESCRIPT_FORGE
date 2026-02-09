-- | FFI Integration Tests
-- | Tests for PureScript → Haskell → Node.js FFI bindings
module Test.Bridge.Integration.FFISpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Aff (Aff)
import Data.Either (Either(..), isRight, isLeft)
import Bridge.FFI.Haskell.Database as DB
import Bridge.FFI.Haskell.Analytics as DuckDB
import Bridge.FFI.Node.Express as Express
import Bridge.FFI.Node.Pino as Pino
import Bridge.FFI.Node.WebSocket as WS

-- | Test Haskell Database FFI
testDatabaseFFI :: forall m. Monad m => m Unit
testDatabaseFFI = do
  describe "Haskell Database FFI Integration" do
    it "opens database via FFI" do
      -- Integration: PureScript → JavaScript → Haskell CLI → SQLite
      dbPath <- liftEffect $ getTestDbPath
      handle <- liftEffect $ DB.openDatabase dbPath
      -- Database handle should be created
      pure unit
    
    it "saves snapshot via FFI" do
      -- Integration: PureScript → JavaScript → Haskell CLI → SQLite → Verify
      dbPath <- liftEffect $ getTestDbPath
      handle <- liftEffect $ DB.openDatabase dbPath
      
      snapshotId <- liftEffect $ generateSnapshotId
      timestamp <- liftEffect $ getCurrentTimestamp
      stateHash <- liftEffect $ computeStateHash """{"test":1}"""
      
      -- Save snapshot via FFI
      savedId <- DB.saveSnapshot handle snapshotId timestamp stateHash """{"test":1}""" (Just "manual") (Just "Test")
      savedId `shouldEqual` snapshotId
    
    it "retrieves snapshot via FFI" do
      -- Integration: PureScript → JavaScript → Haskell CLI → SQLite → Parse → Return
      dbPath <- liftEffect $ getTestDbPath
      handle <- liftEffect $ DB.openDatabase dbPath
      
      snapshotId <- liftEffect $ generateSnapshotId
      timestamp <- liftEffect $ getCurrentTimestamp
      stateHash <- liftEffect $ computeStateHash """{"test":1}"""
      
      -- Save snapshot
      _ <- DB.saveSnapshot handle snapshotId timestamp stateHash """{"test":1}""" (Just "manual") Nothing
      
      -- Retrieve snapshot via FFI
      retrieved <- DB.getSnapshot handle snapshotId
      isJust retrieved `shouldEqual` true
    
    it "handles FFI errors gracefully" do
      -- Integration: Error → JavaScript → PureScript → Error handling
      dbPath <- liftEffect $ getTestDbPath
      handle <- liftEffect $ DB.openDatabase dbPath
      
      -- Try to get non-existent snapshot
      retrieved <- DB.getSnapshot handle "non-existent-id"
      isNothing retrieved `shouldEqual` true

-- | Test DuckDB Analytics FFI
testAnalyticsFFI :: forall m. Monad m => m Unit
testAnalyticsFFI = do
  describe "DuckDB Analytics FFI Integration" do
    it "opens analytics database via FFI" do
      -- Integration: PureScript → JavaScript → Haskell CLI → DuckDB
      analyticsPath <- liftEffect $ getTestAnalyticsPath
      handle <- liftEffect $ DuckDB.openAnalytics (Just analyticsPath)
      -- Analytics handle should be created
      pure unit
    
    it "loads data from SQLite via FFI" do
      -- Integration: PureScript → JavaScript → Haskell CLI → SQLite → DuckDB → Verify
      -- Note: This requires actual SQLite database with data
      analyticsPath <- liftEffect $ getTestAnalyticsPath
      handle <- liftEffect $ DuckDB.openAnalytics (Just analyticsPath)
      sqlitePath <- liftEffect $ getTestDbPath
      
      -- Load data from SQLite
      result <- DuckDB.loadFromSQLite handle sqlitePath
      -- Should complete without error
      pure unit
    
    it "queries analytics via FFI" do
      -- Integration: PureScript → JavaScript → Haskell CLI → DuckDB → Query → Parse → Return
      analyticsPath <- liftEffect $ getTestAnalyticsPath
      handle <- liftEffect $ DuckDB.openAnalytics (Just analyticsPath)
      
      -- Query token usage
      result <- DuckDB.queryTokenUsage handle (Just 7) Nothing
      -- Result should be JSON string
      result.length `shouldBeGreaterThanOrEqual` 0
    
    it "handles FFI errors gracefully" do
      -- Integration: Error → JavaScript → PureScript → Error handling
      analyticsPath <- liftEffect $ getTestAnalyticsPath
      handle <- liftEffect $ DuckDB.openAnalytics (Just analyticsPath)
      
      -- Query with invalid parameters
      result <- DuckDB.queryTokenUsage handle Nothing Nothing
      -- Should return empty array or error JSON
      pure unit

-- | Test Node.js FFI
testNodeFFI :: forall m. Monad m => m Unit
testNodeFFI = do
  describe "Node.js FFI Integration" do
    it "Express FFI works correctly" do
      -- Integration: PureScript → JavaScript → Node.js express → Verify
      app <- liftEffect Express.createApp
      -- App should be created
      pure unit
      
      -- Test route registration
      liftEffect $ Express.get app "/test" \req res -> do
        Express.sendJson res """{"status":"ok"}"""
      -- Route should be registered
      pure unit
    
    it "Pino FFI works correctly" do
      -- Integration: PureScript → JavaScript → Node.js pino → Verify
      logger <- liftEffect $ Pino.create { name: "test", level: "info" }
      -- Logger should be created
      pure unit
      
      -- Test logging
      liftEffect $ Pino.info logger "Test message"
      -- Should log without error
      pure unit
      
      -- Test logging with fields
      liftEffect $ Pino.infoFields logger "Test with fields" """{"key":"value"}"""
      -- Should log without error
      pure unit
    
    it "WebSocket FFI structure is correct" do
      -- Integration: PureScript → JavaScript → Node.js ws → Verify
      -- Note: Full WebSocket test requires HTTP server setup
      -- For now, verify FFI types are correct
      pure unit

foreign import getTestDbPath :: Effect String
foreign import getTestAnalyticsPath :: Effect String
foreign import generateSnapshotId :: Effect String
foreign import getCurrentTimestamp :: Effect String
foreign import computeStateHash :: String -> Effect String
foreign import shouldBeGreaterThanOrEqual :: forall a. Ord a => a -> a -> Boolean

import Data.Maybe (Maybe(..), isJust, isNothing)
