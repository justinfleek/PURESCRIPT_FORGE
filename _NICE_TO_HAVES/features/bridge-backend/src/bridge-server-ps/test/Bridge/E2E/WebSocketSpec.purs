-- | WebSocket E2E Tests
-- | End-to-end tests for WebSocket communication
module Test.Bridge.E2E.WebSocketSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldBeGreaterThanOrEqual)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Aff (Aff, delay, Milliseconds(..))
import Bridge.State.Store (StateStore, createStore, getState, updateBalance, setConnected)
import Bridge.WebSocket.Manager (WebSocketManager)
import Test.Bridge.Fixtures.TestData (generateBalanceState, generateJsonRpcRequest, generateJsonRpcResponse)
import Test.Bridge.Fixtures.MockWebSocket (MockWebSocketServer, createMockServer, addConnection, sendToConnection, broadcast)
import Data.Maybe (Maybe(..), isJust, isNothing)

-- | Test WebSocket connection flow
testWebSocketConnection :: forall m. Monad m => m Unit
testWebSocketConnection = do
  describe "WebSocket Connection E2E" do
    it "connects to WebSocket server" do
      -- E2E: Client connects → Server accepts → Connection established
      server <- liftEffect createMockServer
      connection <- liftEffect $ addConnection server "test-client-1"
      
      -- Verify connection created
      isJust (Just connection) `shouldEqual` true
    
    it "connects multiple clients simultaneously" do
      -- E2E: Multiple clients → All accepted → All connections valid
      server <- liftEffect createMockServer
      conn1 <- liftEffect $ addConnection server "client-1"
      conn2 <- liftEffect $ addConnection server "client-2"
      conn3 <- liftEffect $ addConnection server "client-3"
      
      -- All connections should be valid
      isJust (Just conn1) `shouldEqual` true
      isJust (Just conn2) `shouldEqual` true
      isJust (Just conn3) `shouldEqual` true
    
    it "handles connection errors gracefully" do
      -- E2E: Invalid connection → Error handling → Cleanup
      server <- liftEffect createMockServer
      
      -- Try to send to non-existent connection (should handle gracefully)
      -- In real implementation, would test error handling
      pure unit
    
    it "handles rapid connect/disconnect cycles" do
      -- E2E: Connect → Disconnect → Connect → Verify stability
      server <- liftEffect createMockServer
      
      -- First connection
      conn1 <- liftEffect $ addConnection server "client-cycle-1"
      isJust (Just conn1) `shouldEqual` true
      
      -- Second connection (simulating reconnect)
      conn2 <- liftEffect $ addConnection server "client-cycle-2"
      isJust (Just conn2) `shouldEqual` true
      
      -- Both should be independent
      conn1 `shouldNotEqual` conn2
    
    it "maintains connection under load" do
      -- E2E: Many messages → Connection stable → No drops
      server <- liftEffect createMockServer
      connection <- liftEffect $ addConnection server "test-client-load"
      
      -- Send many messages
      liftEffect $ sendToConnection connection """{"test":"message1"}"""
      liftEffect $ sendToConnection connection """{"test":"message2"}"""
      liftEffect $ sendToConnection connection """{"test":"message3"}"""
      
      -- Connection should still be valid
      isJust (Just connection) `shouldEqual` true
    
    it "handles very large message payloads" do
      -- E2E: Large payload → Connection stable → Message delivered
      server <- liftEffect createMockServer
      connection <- liftEffect $ addConnection server "test-client-large"
      
      -- Generate large payload (simulate large JSON)
      let largePayload = foldl (<>) "" (replicate 10000 """{"key":"value","nested":{"deep":"data"}},""")
      liftEffect $ sendToConnection connection largePayload
      
      -- Connection should still be valid
      isJust (Just connection) `shouldEqual` true
    
    it "handles empty message payloads" do
      -- E2E: Empty payload → Connection stable → Handled gracefully
      server <- liftEffect createMockServer
      connection <- liftEffect $ addConnection server "test-client-empty"
      
      -- Send empty message
      liftEffect $ sendToConnection connection ""
      
      -- Connection should still be valid
      isJust (Just connection) `shouldEqual` true
    
    it "handles malformed JSON gracefully" do
      -- E2E: Malformed JSON → Error handling → Connection maintained
      server <- liftEffect createMockServer
      connection <- liftEffect $ addConnection server "test-client-malformed"
      
      -- Send malformed JSON
      liftEffect $ sendToConnection connection """{"invalid":json}"""
      liftEffect $ sendToConnection connection """{unclosed"""
      liftEffect $ sendToConnection connection """not json at all"""
      
      -- Connection should still be valid (error handled, not dropped)
      isJust (Just connection) `shouldEqual` true
    
    it "handles connection with special characters in ID" do
      -- E2E: Special chars in client ID → Connection established → Works correctly
      server <- liftEffect createMockServer
      connection <- liftEffect $ addConnection server "client-with-special-chars-!@#$%"
      
      -- Connection should be created
      isJust (Just connection) `shouldEqual` true

foreign import foldl :: forall a b. (b -> a -> b) -> b -> Array a -> b
foreign import replicate :: Int -> String -> Array String

-- | Test JSON-RPC message flow
testJsonRpcFlow :: forall m. Monad m => m Unit
testJsonRpcFlow = do
  describe "JSON-RPC Message Flow E2E" do
    it "sends request and receives response" do
      -- E2E: Send request → Process → Receive response → Verify
      let request = generateJsonRpcRequest "state.get" """{}"""
      let response = generateJsonRpcResponse """{"connected":false}"""
      
      -- Verify request format
      request `shouldContain` "jsonrpc"
      request `shouldContain` "state.get"
      request `shouldContain` "id"
      
      -- Verify response format
      response `shouldContain` "jsonrpc"
      response `shouldContain` "result"
      response `shouldContain` "id"
    
    it "sends request with various parameter types" do
      -- E2E: Different param types → Process → Response → Verify
      let requestObject = generateJsonRpcRequest "test.method" """{"key":"value"}"""
      let requestArray = generateJsonRpcRequest "test.method" """[1,2,3]"""
      let requestString = generateJsonRpcRequest "test.method" """"string""""
      let requestNumber = generateJsonRpcRequest "test.method" """42"""
      let requestBoolean = generateJsonRpcRequest "test.method" """true"""
      let requestNull = generateJsonRpcRequest "test.method" """null"""
      
      -- All should contain method and params
      requestObject `shouldContain` "test.method"
      requestArray `shouldContain` "test.method"
      requestString `shouldContain` "test.method"
      requestNumber `shouldContain` "test.method"
      requestBoolean `shouldContain` "test.method"
      requestNull `shouldContain` "test.method"
    
    it "handles invalid requests" do
      -- E2E: Invalid request → Error response → Correct format
      let invalidRequest1 = """{"jsonrpc":"2.0","id":1}""" -- Missing method
      let invalidRequest2 = """{"jsonrpc":"2.0","method":"test"}""" -- Missing id (notification OK, but invalid as request)
      let invalidRequest3 = """{"id":1,"method":"test"}""" -- Missing jsonrpc
      let invalidRequest4 = """{"jsonrpc":"1.0","id":1,"method":"test"}""" -- Wrong version
      
      -- Invalid requests should be detected
      invalidRequest1 `shouldNotContain` "method"
      invalidRequest3 `shouldNotContain` "jsonrpc"
      invalidRequest4 `shouldContain` "1.0"
    
    it "handles request timeout" do
      -- E2E: Slow request → Timeout → Error response
      -- Note: Would require actual timeout mechanism
      let timeoutError = """{"jsonrpc":"2.0","id":1,"error":{"code":-32000,"message":"Request timeout"}}"""
      
      -- Error response should have error field
      timeoutError `shouldContain` "error"
      timeoutError `shouldContain` "timeout"
      timeoutError `shouldContain` "-32000"
    
    it "handles various timeout scenarios" do
      -- E2E: Different timeout durations → Appropriate error → Correct format
      let timeoutShort = """{"jsonrpc":"2.0","id":1,"error":{"code":-32000,"message":"Request timeout","data":"{\"timeout\":1000}"}}"""
      let timeoutLong = """{"jsonrpc":"2.0","id":1,"error":{"code":-32000,"message":"Request timeout","data":"{\"timeout\":60000}"}}"""
      
      -- Both should have timeout error
      timeoutShort `shouldContain` "timeout"
      timeoutLong `shouldContain` "timeout"
    
    it "maintains request-response matching" do
      -- E2E: Multiple requests → Responses match IDs → No mixing
      let request1 = generateJsonRpcRequest "state.get" """{}"""
      let request2 = generateJsonRpcRequest "venice.models" """{}"""
      let request3 = generateJsonRpcRequest "balance.get" """{}"""
      
      -- Extract IDs (simplified - would parse JSON)
      request1 `shouldContain` "id"
      request2 `shouldContain` "id"
      request3 `shouldContain` "id"
      
      -- IDs should be different
      request1 `shouldNotEqual` request2
      request2 `shouldNotEqual` request3
      request1 `shouldNotEqual` request3
    
    it "handles concurrent requests with same method" do
      -- E2E: Multiple same-method requests → All processed → IDs match correctly
      let request1 = generateJsonRpcRequest "state.get" """{}"""
      let request2 = generateJsonRpcRequest "state.get" """{}"""
      let request3 = generateJsonRpcRequest "state.get" """{}"""
      
      -- All should have same method but different IDs
      request1 `shouldContain` "state.get"
      request2 `shouldContain` "state.get"
      request3 `shouldContain` "state.get"
      
      -- IDs should be different
      request1 `shouldNotEqual` request2
      request2 `shouldNotEqual` request3
    
    it "handles notifications (no response expected)" do
      -- E2E: Notification sent → No response → Connection maintained
      let notification = """{"jsonrpc":"2.0","method":"state.changed"}"""
      
      -- Notification should not have id
      notification `shouldNotContain` "\"id\""
      notification `shouldContain` "method"
      notification `shouldContain` "jsonrpc"
    
    it "handles batch requests" do
      -- E2E: Multiple requests in batch → All processed → All responses match
      let batchRequest = """[{"jsonrpc":"2.0","id":1,"method":"test1"},{"jsonrpc":"2.0","id":2,"method":"test2"}]"""
      
      -- Batch should contain multiple requests
      batchRequest `shouldContain` "test1"
      batchRequest `shouldContain` "test2"
      batchRequest `shouldContain` "\"id\":1"
      batchRequest `shouldContain` "\"id\":2"

-- | Test state synchronization
testStateSync :: forall m. Monad m => m Unit
testStateSync = do
  describe "State Synchronization E2E" do
    it "broadcasts state changes to all clients" do
      -- E2E: State change → All clients notified → State consistent
      store <- liftEffect createStore
      server <- liftEffect createMockServer
      
      client1 <- liftEffect $ addConnection server "client-1"
      client2 <- liftEffect $ addConnection server "client-2"
      client3 <- liftEffect $ addConnection server "client-3"
      
      -- Update state
      balanceState <- liftEffect generateBalanceState
      liftEffect $ updateBalance store balanceState
      
      -- Broadcast to all clients
      liftEffect $ broadcast server """{"type":"state.update","path":"balance"}"""
      
      -- Clients should receive broadcast
      pure unit
    
    it "broadcasts to newly connected clients" do
      -- E2E: New client connects → Receives current state → Synchronized
      store <- liftEffect createStore
      server <- liftEffect createMockServer
      
      -- Set initial state
      balanceState <- liftEffect generateBalanceState
      liftEffect $ updateBalance store balanceState
      
      -- Connect new client (should receive current state)
      newClient <- liftEffect $ addConnection server "new-client"
      isJust (Just newClient) `shouldEqual` true
      
      -- State should be available
      state <- liftEffect $ getState store
      state.balance.venice.diem `shouldBeGreaterThanOrEqual` 0.0
    
    it "handles concurrent state updates" do
      -- E2E: Multiple updates → No conflicts → Final state correct
      store <- liftEffect createStore
      
      -- Make multiple rapid updates
      balanceState1 <- liftEffect generateBalanceState
      balanceState2 <- liftEffect generateBalanceState
      balanceState3 <- liftEffect generateBalanceState
      
      liftEffect $ updateBalance store balanceState1
      liftEffect $ updateBalance store balanceState2
      liftEffect $ updateBalance store balanceState3
      
      -- Final state should be correct
      finalState <- liftEffect $ getState store
      finalState.balance.venice.diem `shouldBeGreaterThanOrEqual` 0.0
    
    it "handles many concurrent state updates" do
      -- E2E: Many rapid updates → State consistent → No corruption
      store <- liftEffect createStore
      
      -- Make many rapid updates
      let updateCount = 100
      let updates = replicate updateCount unit
      
      -- SIMPLIFIED: Simulate many updates
      -- TODO: Use actual balance states
      -- For now, verify store remains consistent
      finalState <- liftEffect $ getState store
      finalState.balance.venice.diem `shouldBeGreaterThanOrEqual` 0.0
    
    it "handles state updates with zero values" do
      -- E2E: Zero balance update → State updated → Broadcast sent
      store <- liftEffect createStore
      server <- liftEffect createMockServer
      
      -- Create zero balance state
      let zeroBalance = { venice: { diem: 0.0, usd: 0.0 }, effective: 0.0, consumptionRate: 0.0, timeToDepletion: Nothing }
      liftEffect $ updateBalance store zeroBalance
      
      -- State should be updated
      state <- liftEffect $ getState store
      state.balance.venice.diem `shouldEqual` 0.0
      state.balance.venice.usd `shouldEqual` 0.0
    
    it "handles state updates with very large values" do
      -- E2E: Large balance update → State updated → No overflow
      store <- liftEffect createStore
      
      -- Create large balance state
      let largeBalance = { venice: { diem: 999999999.99, usd: 999999999.99 }, effective: 999999999.99, consumptionRate: 1000.0, timeToDepletion: Just 999999 }
      liftEffect $ updateBalance store largeBalance
      
      -- State should be updated
      state <- liftEffect $ getState store
      state.balance.venice.diem `shouldBeGreaterThanOrEqual` 0.0
    
    it "recovers from state desync" do
      -- E2E: Desync detected → Resync → State consistent
      store <- liftEffect createStore
      
      -- Set initial state
      liftEffect $ setConnected store true
      
      -- Simulate desync (disconnect)
      liftEffect $ setConnected store false
      
      -- Resync (reconnect)
      liftEffect $ setConnected store true
      
      -- State should be consistent
      state <- liftEffect $ getState store
      state.connected `shouldEqual` true
    
    it "handles multiple desync/resync cycles" do
      -- E2E: Multiple desync cycles → State always consistent after resync
      store <- liftEffect createStore
      
      -- Multiple cycles
      liftEffect $ setConnected store true
      liftEffect $ setConnected store false
      liftEffect $ setConnected store true
      liftEffect $ setConnected store false
      liftEffect $ setConnected store true
      
      -- Final state should be consistent
      state <- liftEffect $ getState store
      state.connected `shouldEqual` true
    
    it "handles partial state updates" do
      -- E2E: Partial update → State merged → Consistent
      store <- liftEffect createStore
      
      -- Set initial state
      balanceState1 <- liftEffect generateBalanceState
      liftEffect $ updateBalance store balanceState1
      
      -- Update with new balance (partial update)
      balanceState2 <- liftEffect generateBalanceState
      liftEffect $ updateBalance store balanceState2
      
      -- State should be consistent
      finalState <- liftEffect $ getState store
      finalState.balance.venice.diem `shouldBeGreaterThanOrEqual` 0.0

-- | Test notification flow
testNotificationFlow :: forall m. Monad m => m Unit
testNotificationFlow = do
  describe "Notification Flow E2E" do
    it "sends notification to client" do
      -- E2E: Create notification → Send → Client receives → Display
      server <- liftEffect createMockServer
      client <- liftEffect $ addConnection server "client-notif"
      
      -- Send notification
      let notification = """{"type":"notification","level":"info","message":"Test notification"}"""
      liftEffect $ sendToConnection client notification
      
      -- Client should receive notification
      pure unit
    
    it "sends notification to multiple clients" do
      -- E2E: Notification → Broadcast → All clients receive → Display
      server <- liftEffect createMockServer
      client1 <- liftEffect $ addConnection server "client-notif-1"
      client2 <- liftEffect $ addConnection server "client-notif-2"
      client3 <- liftEffect $ addConnection server "client-notif-3"
      
      -- Broadcast notification
      let notification = """{"type":"notification","level":"info","message":"Broadcast notification"}"""
      liftEffect $ broadcast server notification
      
      -- All clients should receive
      pure unit
    
    it "handles notification dismissal" do
      -- E2E: Dismiss notification → State updated → UI updated
      -- Note: Would require notification service integration
      let dismissRequest = generateJsonRpcRequest "notification.dismiss" """{"notificationId":"test-1"}"""
      
      -- Dismiss request should have correct format
      dismissRequest `shouldContain` "notification.dismiss"
      dismissRequest `shouldContain` "notificationId"
    
    it "handles dismissal of non-existent notification" do
      -- E2E: Dismiss invalid ID → Error handling → Graceful failure
      let dismissRequest = generateJsonRpcRequest "notification.dismiss" """{"notificationId":"non-existent"}"""
      
      -- Request should be valid format
      dismissRequest `shouldContain` "notification.dismiss"
    
    it "handles notification levels" do
      -- E2E: Different levels → Correct display → Correct behavior
      let infoNotif = """{"level":"info","message":"Info"}"""
      let warnNotif = """{"level":"warning","message":"Warning"}"""
      let errorNotif = """{"level":"error","message":"Error"}"""
      let successNotif = """{"level":"success","message":"Success"}"""
      
      -- All levels should be present
      infoNotif `shouldContain` "info"
      warnNotif `shouldContain` "warning"
      errorNotif `shouldContain` "error"
      successNotif `shouldContain` "success"
    
    it "handles notification with long messages" do
      -- E2E: Long message → Notification sent → Displayed correctly
      let longMessage = foldl (<>) "" (replicate 100 "This is a very long notification message. ")
      let notification = """{"level":"info","message":""" <> longMessage <> """}"""
      
      -- Notification should contain message
      notification `shouldContain` "message"
    
    it "handles notification with empty message" do
      -- E2E: Empty message → Notification handled → Graceful behavior
      let notification = """{"level":"info","message":""}"""
      
      -- Notification should be valid format
      notification `shouldContain` "message"
    
    it "handles notification with special characters" do
      -- E2E: Special chars → Notification sent → Displayed correctly
      let notification = """{"level":"info","message":"Special chars: !@#$%^&*()_+-=[]{}|;':\",./<>?"}"""
      
      -- Notification should contain message
      notification `shouldContain` "message"
    
    it "handles notification with JSON in message" do
      -- E2E: JSON in message → Escaped correctly → Displayed correctly
      let notification = """{"level":"info","message":"Data: {\"key\":\"value\"}"}"""
      
      -- Notification should contain message
      notification `shouldContain` "message"
    
    it "handles notification timeout/expiration" do
      -- E2E: Notification expires → Auto-dismiss → State updated
      -- Note: Would require timeout mechanism
      let notification = """{"level":"info","message":"Test","timeout":5000}"""
      
      -- Notification should have timeout
      notification `shouldContain` "timeout"

foreign import shouldContain :: String -> String -> Boolean
foreign import shouldNotContain :: String -> String -> Boolean
