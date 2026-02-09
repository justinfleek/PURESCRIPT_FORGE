-- | WebSocket FFI Tests
-- | Unit and property tests for WebSocket FFI bindings
module Test.Sidepanel.FFI.WebSocketSpec where

import Prelude
import Effect.Class (liftEffect)
import Test.Spec (Spec, describe, it, pending)
import Test.Spec.Assertions (shouldEqual)
import Test.QuickCheck (quickCheck)
import Sidepanel.FFI.WebSocket
  ( toReadyState
  , ReadyState(..)
  )

-- | Test WebSocket creation
testWebSocketCreation :: Spec Unit
testWebSocketCreation =
  describe "WebSocket Creation" do
    pending "creates WebSocket connection (requires WebSocket server)"

-- | Test ready state
testReadyState :: Spec Unit
testReadyState =
  describe "Ready State" do
    it "converts ready state int to type" do
      toReadyState 0 `shouldEqual` Connecting
      toReadyState 1 `shouldEqual` Open
      toReadyState 2 `shouldEqual` Closing
      toReadyState 3 `shouldEqual` Closed
      toReadyState 4 `shouldEqual` Closed

    pending "gets ready state from connection (requires WebSocket server)"

-- | Test message operations
testMessageOperations :: Spec Unit
testMessageOperations =
  describe "Message Operations" do
    pending "sends messages (requires WebSocket server)"
    pending "handles send errors (requires WebSocket server)"

-- | Test connection operations
testConnectionOperations :: Spec Unit
testConnectionOperations =
  describe "Connection Operations" do
    pending "closes connection (requires WebSocket server)"
    pending "closes connection with code and reason (requires WebSocket server)"

-- | Test event handlers
testEventHandlers :: Spec Unit
testEventHandlers =
  describe "Event Handlers" do
    pending "sets onopen handler (requires WebSocket server)"
    pending "sets onclose handler (requires WebSocket server)"
    pending "sets onerror handler (requires WebSocket server)"
    pending "sets onmessage handler (requires WebSocket server)"

-- | Property: Ready state conversion is total
prop_readyStateConversionTotal :: Int -> Boolean
prop_readyStateConversionTotal n =
  case toReadyState n of
    Connecting -> true
    Open -> true
    Closing -> true
    Closed -> true

-- | Property tests
testProperties :: Spec Unit
testProperties =
  describe "Property Tests" do
    it "ready state conversion is total" do
      liftEffect $ quickCheck prop_readyStateConversionTotal
