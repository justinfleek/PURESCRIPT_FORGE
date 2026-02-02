-- | Mock WebSocket Server
-- | Test fixture for WebSocket testing
module Test.Bridge.Fixtures.MockWebSocket where

import Prelude
import Effect (Effect)
import Effect.Ref (Ref, new, read, write)
import Data.Array (Array)
import Bridge.WebSocket.Manager (WebSocketManager)

-- | Mock WebSocket connection
type MockConnection =
  { id :: String
  , messages :: Ref (Array String)
  , connected :: Ref Boolean
  }

-- | Create mock WebSocket server
createMockServer :: Effect MockWebSocketServer
createMockServer = do
  connections <- new []
  pure { connections }

type MockWebSocketServer =
  { connections :: Ref (Array MockConnection)
  }

-- | Add mock connection
addConnection :: MockWebSocketServer -> String -> Effect MockConnection
addConnection server id = do
  messages <- new []
  connected <- new true
  let conn = { id, messages, connected }
  modify_ (\conns -> conns <> [conn]) server.connections
  pure conn

-- | Send message to mock connection
sendToConnection :: MockConnection -> String -> Effect Unit
sendToConnection conn message = do
  modify_ (\msgs -> msgs <> [message]) conn.messages

-- | Broadcast to all connections
broadcast :: MockWebSocketServer -> String -> Effect Unit
broadcast server message = do
  conns <- read server.connections
  traverse_ (\conn -> sendToConnection conn message) conns

foreign import modify_ :: forall a. (a -> a) -> Ref a -> Effect Unit

-- | Mock WebSocket server (simplified for testing)
foreign import data MockWebSocketServer :: Type

foreign import createMockServer :: Effect MockWebSocketServer
foreign import addConnection :: MockWebSocketServer -> String -> Effect MockConnection
foreign import sendToConnection :: MockConnection -> String -> Effect Unit
foreign import broadcast :: MockWebSocketServer -> String -> Effect Unit
