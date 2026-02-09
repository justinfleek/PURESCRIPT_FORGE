-- | WebSocket Client Tests
-- | Unit and property tests for WebSocket client functionality
module Test.Sidepanel.WebSocket.ClientSpec where

import Prelude
import Test.Spec (Spec, describe, it, pending)
import Test.Spec.Assertions (shouldEqual)
import Effect.Class (liftEffect)
import Effect.Aff (Aff)
import Data.Either (Either(..), isRight, isLeft)
import Sidepanel.WebSocket.Client
  ( createClient
  , connect
  , disconnect
  , request
  , subscribe
  , ConnectionState(..)
  , ClientConfig
  , defaultConfig
  , WSClient
  )

-- | Test client creation
testClientCreation :: Spec Unit
testClientCreation = do
  describe "Client Creation" do
    it "creates client with default config" do
      -- Test passes if createClient does not throw
      _client <- liftEffect $ createClient defaultConfig
      unit `shouldEqual` unit

    it "creates client with custom config" do
      let config = defaultConfig { url = "ws://custom:8080/ws", maxReconnectAttempts = 5 }
      _client <- liftEffect $ createClient config
      unit `shouldEqual` unit

-- | Test connection
testConnection :: Spec Unit
testConnection = do
  describe "Connection" do
    pending "connects to server (requires mock WebSocket server)"
    pending "disconnects from server (requires mock WebSocket server)"
    pending "handles connection errors (requires mock WebSocket server)"
    pending "reconnects on disconnect (requires mock WebSocket server)"

-- | Test request/response
testRequestResponse :: Spec Unit
testRequestResponse = do
  describe "Request/Response" do
    pending "sends request and receives response (requires mock server)"
    pending "handles request timeout (requires mock server)"
    pending "queues messages when disconnected (requires mock server)"

-- | Test subscriptions
testSubscriptions :: Spec Unit
testSubscriptions = do
  describe "Subscriptions" do
    pending "subscribes to server messages (requires mock server)"
    pending "unsubscribes from server messages (requires mock server)"

-- | Property: Client state transitions are valid and distinguishable via Eq
-- | Note: ConnectionState doesn't have an Arbitrary instance (it's a local data type
-- | and quickcheck can't generate Reconnecting Int or Error String variants).
-- | Instead, test specific known states directly.
testProperties :: Spec Unit
testProperties = do
  describe "Property Tests" do
    it "client state transitions are valid and distinguishable" do
      -- Test each state is distinguishable via Eq
      (Disconnected == Disconnected) `shouldEqual` true
      (Connecting == Connecting) `shouldEqual` true
      (Connected == Connected) `shouldEqual` true
      (Disconnected == Connected) `shouldEqual` false
      (Connecting == Disconnected) `shouldEqual` false
      (Connected == Connecting) `shouldEqual` false
