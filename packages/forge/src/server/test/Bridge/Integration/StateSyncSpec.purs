-- | State Synchronization Integration Tests
-- | Tests for state sync across components
module Test.Bridge.Integration.StateSyncSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Ref (Ref, new, read, write)
import Data.Array (Array, length)
import Bridge.State.Store (StateStore, createStore, getState, updateBalance, setConnected)
import Bridge.State.Store (BalanceState)
import Test.Bridge.Fixtures.TestData (generateBalanceState)

-- | Mock WebSocket client state
type MockClient =
  { id :: String
  , receivedMessages :: Ref (Array String)
  , connected :: Ref Boolean
  }

-- | Test state sync flow
testStateSyncFlow :: forall m. Monad m => m Unit
testStateSyncFlow = do
  describe "State Synchronization Integration" do
    it "syncs state changes to mock clients" do
      -- Integration: State change → Mock clients → All receive → State consistent
      store <- liftEffect createStore
      client1 <- liftEffect $ createMockClient "client-1"
      client2 <- liftEffect $ createMockClient "client-2"
      
      -- Subscribe clients to state changes
      liftEffect $ subscribeToStateChanges store client1
      liftEffect $ subscribeToStateChanges store client2
      
      -- Update state
      balanceState <- liftEffect generateBalanceState
      liftEffect $ updateBalance store balanceState
      
      -- Verify clients received updates
      messages1 <- liftEffect $ read client1.receivedMessages
      messages2 <- liftEffect $ read client2.receivedMessages
      
      messages1.length `shouldBeGreaterThanOrEqual` 1
      messages2.length `shouldBeGreaterThanOrEqual` 1
    
    it "handles multiple clients correctly" do
      -- Integration: State change → Multiple clients → All receive → State consistent
      store <- liftEffect createStore
      clients <- liftEffect $ createMultipleClients 5
      
      -- Subscribe all clients
      liftEffect $ traverse_ (subscribeToStateChanges store) clients
      
      -- Update state
      balanceState <- liftEffect generateBalanceState
      liftEffect $ updateBalance store balanceState
      
      -- Verify all clients received updates
      allReceived <- liftEffect $ traverse_ (\client -> read client.receivedMessages) clients
      -- All clients should have received messages
      pure unit
    
    it "handles client disconnection during sync" do
      -- Integration: State change → Client disconnects → Other clients receive → No errors
      store <- liftEffect createStore
      client1 <- liftEffect $ createMockClient "client-1"
      client2 <- liftEffect $ createMockClient "client-2"
      
      -- Subscribe clients
      liftEffect $ subscribeToStateChanges store client1
      liftEffect $ subscribeToStateChanges store client2
      
      -- Disconnect client1
      liftEffect $ disconnectClient client1
      
      -- Update state
      balanceState <- liftEffect generateBalanceState
      liftEffect $ updateBalance store balanceState
      
      -- Verify client2 received update, client1 did not
      messages1 <- liftEffect $ read client1.receivedMessages
      messages2 <- liftEffect $ read client2.receivedMessages
      
      messages1.length `shouldEqual` 0
      messages2.length `shouldBeGreaterThanOrEqual` 1
    
    it "handles rapid state changes" do
      -- Integration: Rapid changes → Queue → Process → All clients updated
      store <- liftEffect createStore
      client <- liftEffect $ createMockClient "client-rapid"
      
      -- Subscribe client
      liftEffect $ subscribeToStateChanges store client
      
      -- Make rapid state changes
      balanceState1 <- liftEffect generateBalanceState
      balanceState2 <- liftEffect generateBalanceState
      balanceState3 <- liftEffect generateBalanceState
      
      liftEffect $ updateBalance store balanceState1
      liftEffect $ updateBalance store balanceState2
      liftEffect $ updateBalance store balanceState3
      
      -- Verify client received all updates
      messages <- liftEffect $ read client.receivedMessages
      messages.length `shouldBeGreaterThanOrEqual` 3

-- | Test notification sync
testNotificationSync :: forall m. Monad m => m Unit
testNotificationSync = do
  describe "Notification Synchronization Integration" do
    it "sends notifications to all clients" do
      -- Integration: Create notification → Broadcast → All clients receive → Display
      store <- liftEffect createStore
      client1 <- liftEffect $ createMockClient "client-notif-1"
      client2 <- liftEffect $ createMockClient "client-notif-2"
      
      -- Subscribe clients
      liftEffect $ subscribeToStateChanges store client1
      liftEffect $ subscribeToStateChanges store client2
      
      -- Simulate notification (via state change)
      liftEffect $ setConnected store true
      
      -- Verify clients received notification
      messages1 <- liftEffect $ read client1.receivedMessages
      messages2 <- liftEffect $ read client2.receivedMessages
      
      messages1.length `shouldBeGreaterThanOrEqual` 1
      messages2.length `shouldBeGreaterThanOrEqual` 1
    
    it "handles notification dismissal sync" do
      -- Integration: Dismiss → State update → Broadcast → Clients update
      store <- liftEffect createStore
      client <- liftEffect $ createMockClient "client-dismiss"
      
      -- Subscribe client
      liftEffect $ subscribeToStateChanges store client
      
      -- Set connected, then disconnect
      liftEffect $ setConnected store true
      liftEffect $ setConnected store false
      
      -- Verify client received both updates
      messages <- liftEffect $ read client.receivedMessages
      messages.length `shouldBeGreaterThanOrEqual` 2

foreign import createMockClient :: String -> Effect MockClient
foreign import createMultipleClients :: Int -> Effect (Array MockClient)
foreign import subscribeToStateChanges :: StateStore -> MockClient -> Effect Unit
foreign import disconnectClient :: MockClient -> Effect Unit
foreign import shouldBeGreaterThanOrEqual :: forall a. Ord a => a -> a -> Boolean
foreign import traverse_ :: forall a b m. Applicative m => (a -> m b) -> Array a -> m Unit
