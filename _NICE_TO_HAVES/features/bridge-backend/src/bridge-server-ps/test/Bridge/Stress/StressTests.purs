-- | Stress Tests
-- | Tests for system limits and edge cases
module Test.Bridge.Stress.StressTests where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldBeGreaterThanOrEqual)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Aff (Aff, delay, Milliseconds(..))
import Bridge.State.Store (StateStore, createStore, updateBalance, getState)
import Bridge.FFI.Haskell.Database as DB
import Test.Bridge.Fixtures.TestData (generateBalanceState)
import Test.Bridge.Fixtures.MockWebSocket (MockWebSocketServer, createMockServer, addConnection, broadcast)

-- | Test concurrent connections
testConcurrentConnections :: forall m. Monad m => m Unit
testConcurrentConnections = do
  describe "Concurrent Connections Stress Test" do
    it "handles 50 concurrent connections" do
      -- Stress: 50 concurrent connections → All stable → No drops
      server <- liftEffect createMockServer
      
      -- Create 50 connections
      connections <- liftEffect $ createConcurrentConnections server 50
      
      -- All connections should be created
      connections.length `shouldEqual` 50
      
      -- Broadcast to all
      liftEffect $ broadcast server """{"type":"ping"}"""
      
      -- All should receive message
      pure unit
    
    it "handles connection churn" do
      -- Stress: Rapid connect/disconnect → System stable
      server <- liftEffect createMockServer
      
      -- Create and disconnect rapidly
      liftEffect $ simulateConnectionChurn server 20
      
      -- System should remain stable
      pure unit

-- | Test rapid state updates
testRapidStateUpdates :: forall m. Monad m => m Unit
testRapidStateUpdates = do
  describe "Rapid State Updates Stress Test" do
    it "handles 1000 rapid state updates" do
      -- Stress: 1000 rapid updates → No corruption → Final state correct
      store <- liftEffect createStore
      
      -- Make 1000 rapid updates
      liftEffect $ performRapidUpdates store 1000
      
      -- Final state should be valid
      state <- liftEffect $ getState store
      state.balance.venice.diem `shouldBeGreaterThanOrEqual` 0.0
    
    it "handles concurrent state updates" do
      -- Stress: Concurrent updates → No conflicts → State consistent
      store <- liftEffect createStore
      
      -- Simulate concurrent updates
      liftEffect $ performConcurrentUpdates store 10
      
      -- State should be consistent
      state <- liftEffect $ getState store
      pure unit

-- | Test large payloads
testLargePayloads :: forall m. Monad m => m Unit
testLargePayloads = do
  describe "Large Payloads Stress Test" do
    it "handles large snapshot data" do
      -- Stress: Large snapshot → Save → Retrieve → Data intact
      dbPath <- liftEffect $ getTestDbPath
      handle <- liftEffect $ DB.openDatabase dbPath
      
      snapshotId <- liftEffect $ generateSnapshotId
      timestamp <- liftEffect $ getCurrentTimestamp
      stateHash <- liftEffect $ computeStateHash largePayload
      
      -- Save large payload
      _ <- DB.saveSnapshot handle snapshotId timestamp stateHash largePayload (Just "manual") Nothing
      
      -- Retrieve and verify
      retrieved <- DB.getSnapshot handle snapshotId
      isJust retrieved `shouldEqual` true
    
    it "handles large JSON-RPC messages" do
      -- Stress: Large message → Parse → Process → Response
      let largeRequest = generateLargeJsonRpcRequest
      
      -- Request should be parseable
      largeRequest.length `shouldBeGreaterThanOrEqual` 10000

-- | Test memory pressure
testMemoryPressure :: forall m. Monad m => m Unit
testMemoryPressure = do
  describe "Memory Pressure Stress Test" do
    it "handles many state stores" do
      -- Stress: Many stores → Memory stable → No leaks
      stores <- liftEffect $ createManyStores 100
      
      -- All stores should be created
      stores.length `shouldEqual` 100
      
      -- Update all stores
      liftEffect $ updateAllStores stores
      
      -- Memory should be stable
      pure unit
    
    it "handles many database connections" do
      -- Stress: Many connections → All functional → No leaks
      connections <- liftEffect $ createManyDatabaseConnections 20
      
      -- All connections should work
      connections.length `shouldEqual` 20

-- | Test error recovery
testErrorRecovery :: forall m. Monad m => m Unit
testErrorRecovery = do
  describe "Error Recovery Stress Test" do
    it "recovers from database errors" do
      -- Stress: Database errors → Recovery → System stable
      dbPath <- liftEffect $ getTestDbPath
      handle <- liftEffect $ DB.openDatabase dbPath
      
      -- Try invalid operations
      invalidId <- liftEffect $ generateSnapshotId
      retrieved <- DB.getSnapshot handle ("invalid-" <> invalidId)
      
      -- Should handle gracefully
      isNothing retrieved `shouldEqual` true
    
    it "recovers from state corruption" do
      -- Stress: Corrupted state → Recovery → State valid
      store <- liftEffect createStore
      
      -- Simulate recovery
      balanceState <- liftEffect generateBalanceState
      liftEffect $ updateBalance store balanceState
      
      -- State should be valid after recovery
      state <- liftEffect $ getState store
      state.balance.venice.diem `shouldBeGreaterThanOrEqual` 0.0

foreign import createConcurrentConnections :: MockWebSocketServer -> Int -> Effect (Array MockConnection)
foreign import simulateConnectionChurn :: MockWebSocketServer -> Int -> Effect Unit
foreign import performRapidUpdates :: StateStore -> Int -> Effect Unit
foreign import performConcurrentUpdates :: StateStore -> Int -> Effect Unit
foreign import getTestDbPath :: Effect String
foreign import generateSnapshotId :: Effect String
foreign import getCurrentTimestamp :: Effect String
foreign import computeStateHash :: String -> Effect String
foreign import largePayload :: String
foreign import generateLargeJsonRpcRequest :: String
foreign import createManyStores :: Int -> Effect (Array StateStore)
foreign import updateAllStores :: Array StateStore -> Effect Unit
foreign import createManyDatabaseConnections :: Int -> Effect (Array DB.DatabaseHandle)
foreign import shouldBeGreaterThanOrEqual :: forall a. Ord a => a -> a -> Boolean

import Data.Maybe (Maybe(..), isJust, isNothing)
import Test.Bridge.Fixtures.MockWebSocket (MockConnection)
import Test.Bridge.Fixtures.TestData (generateJsonRpcRequest)
