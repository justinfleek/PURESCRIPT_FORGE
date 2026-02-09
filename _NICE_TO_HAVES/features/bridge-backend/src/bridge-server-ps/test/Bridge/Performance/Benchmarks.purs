-- | Performance Benchmarks
-- | Performance tests for critical paths
module Test.Bridge.Performance.Benchmarks where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldBeLessThan)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Aff (Aff, delay, Milliseconds(..))
import Bridge.State.Store (StateStore, createStore, updateBalance, updateSession, getState)
import Bridge.FFI.Haskell.Database as DB
import Test.Bridge.Fixtures.TestData (generateBalanceState, generateSessionState)

-- | Performance targets (milliseconds)
type PerformanceTargets =
  { stateUpdate :: Number
  , databaseSave :: Number
  , databaseQuery :: Number
  , stateSync :: Number
  , jsonRpcRequest :: Number
  }

-- | Default performance targets
defaultTargets :: PerformanceTargets
defaultTargets =
  { stateUpdate: 10.0
  , databaseSave: 50.0
  , databaseQuery: 30.0
  , stateSync: 100.0
  , jsonRpcRequest: 50.0
  }

-- | Benchmark state update performance
benchmarkStateUpdate :: forall m. Monad m => m Unit
benchmarkStateUpdate = do
  describe "State Update Performance" do
    it "state update is fast" do
      store <- liftEffect createStore
      balanceState <- liftEffect generateBalanceState
      
      -- Measure update time
      startTime <- liftEffect getCurrentTimeMs
      liftEffect $ updateBalance store balanceState
      endTime <- liftEffect getCurrentTimeMs
      
      let duration = endTime - startTime
      duration `shouldBeLessThan` defaultTargets.stateUpdate
    
    it "concurrent state updates are fast" do
      store <- liftEffect createStore
      
      -- Make multiple rapid updates
      startTime <- liftEffect getCurrentTimeMs
      balanceState1 <- liftEffect generateBalanceState
      balanceState2 <- liftEffect generateBalanceState
      balanceState3 <- liftEffect generateBalanceState
      
      liftEffect $ updateBalance store balanceState1
      liftEffect $ updateBalance store balanceState2
      liftEffect $ updateBalance store balanceState3
      endTime <- liftEffect getCurrentTimeMs
      
      let duration = endTime - startTime
      duration `shouldBeLessThan` (defaultTargets.stateUpdate * 3.0)

-- | Benchmark database operations
benchmarkDatabaseOperations :: forall m. Monad m => m Unit
benchmarkDatabaseOperations = do
  describe "Database Operations Performance" do
    it "database save is fast" do
      dbPath <- liftEffect $ getTestDbPath
      handle <- liftEffect $ DB.openDatabase dbPath
      
      snapshotId <- liftEffect $ generateSnapshotId
      timestamp <- liftEffect $ getCurrentTimestamp
      stateHash <- liftEffect $ computeStateHash """{"test":1}"""
      
      -- Measure save time
      startTime <- liftEffect getCurrentTimeMs
      _ <- DB.saveSnapshot handle snapshotId timestamp stateHash """{"test":1}""" (Just "manual") Nothing
      endTime <- liftEffect getCurrentTimeMs
      
      let duration = endTime - startTime
      duration `shouldBeLessThan` defaultTargets.databaseSave
    
    it "database query is fast" do
      dbPath <- liftEffect $ getTestDbPath
      handle <- liftEffect $ DB.openDatabase dbPath
      
      -- Save first
      snapshotId <- liftEffect $ generateSnapshotId
      timestamp <- liftEffect $ getCurrentTimestamp
      stateHash <- liftEffect $ computeStateHash """{"test":1}"""
      _ <- DB.saveSnapshot handle snapshotId timestamp stateHash """{"test":1}""" (Just "manual") Nothing
      
      -- Measure query time
      startTime <- liftEffect getCurrentTimeMs
      _ <- DB.getSnapshot handle snapshotId
      endTime <- liftEffect getCurrentTimeMs
      
      let duration = endTime - startTime
      duration `shouldBeLessThan` defaultTargets.databaseQuery

-- | Benchmark state synchronization
benchmarkStateSync :: forall m. Monad m => m Unit
benchmarkStateSync = do
  describe "State Synchronization Performance" do
    it "state sync to multiple clients is fast" do
      store <- liftEffect createStore
      
      -- Create multiple mock clients
      clients <- liftEffect $ createMultipleClients 10
      
      -- Subscribe all clients
      liftEffect $ traverse_ (subscribeToStateChanges store) clients
      
      -- Measure sync time
      startTime <- liftEffect getCurrentTimeMs
      balanceState <- liftEffect generateBalanceState
      liftEffect $ updateBalance store balanceState
      endTime <- liftEffect getCurrentTimeMs
      
      let duration = endTime - startTime
      duration `shouldBeLessThan` defaultTargets.stateSync

-- | Benchmark JSON-RPC request handling
benchmarkJsonRpcRequest :: forall m. Monad m => m Unit
benchmarkJsonRpcRequest = do
  describe "JSON-RPC Request Performance" do
    it "JSON-RPC request handling is fast" do
      -- Measure request parsing and response generation
      let request = """{"jsonrpc":"2.0","id":1,"method":"state.get","params":{}}"""
      
      startTime <- liftEffect getCurrentTimeMs
      -- Parse request (simplified)
      _ <- liftEffect $ parseJsonRpcRequest request
      endTime <- liftEffect getCurrentTimeMs
      
      let duration = endTime - startTime
      duration `shouldBeLessThan` defaultTargets.jsonRpcRequest

foreign import getCurrentTimeMs :: Effect Number
foreign import getTestDbPath :: Effect String
foreign import generateSnapshotId :: Effect String
foreign import getCurrentTimestamp :: Effect String
foreign import computeStateHash :: String -> Effect String
foreign import createMultipleClients :: Int -> Effect (Array MockClient)
foreign import subscribeToStateChanges :: StateStore -> MockClient -> Effect Unit
foreign import parseJsonRpcRequest :: String -> Effect Unit
foreign import shouldBeLessThan :: forall a. Ord a => a -> a -> Boolean
foreign import traverse_ :: forall a b m. Applicative m => (a -> m b) -> Array a -> m Unit

import Test.Bridge.Integration.StateSyncSpec (MockClient)
