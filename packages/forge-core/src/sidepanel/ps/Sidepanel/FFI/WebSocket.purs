-- | WebSocket FFI Module - WebSocket Connection Bindings
-- |
-- | **What:** Provides FFI bindings for browser WebSocket API, enabling real-time
-- |         bidirectional communication with the Bridge Server.
-- | **Why:** Enables real-time updates from Bridge Server (notifications, state changes,
-- |         balance updates) and allows sending commands/requests to the server.
-- | **How:** Uses foreign function imports to wrap browser WebSocket API, providing
-- |         PureScript-friendly types and Effect-based operations. Handles connection lifecycle,
-- |         message sending/receiving, and event callbacks.
-- |
-- | **Dependencies:** None (pure FFI bindings)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.FFI.WebSocket as WS
-- |
-- | -- Create connection
-- | ws <- liftEffect $ WS.create "ws://localhost:4096/ws"
-- |
-- | -- Set handlers
-- | liftEffect $ WS.onOpen ws \_ -> handleOpen
-- | liftEffect $ WS.onMessage ws \msg -> handleMessage msg
-- | liftEffect $ WS.onError ws \err -> handleError err
-- |
-- | -- Send message
-- | result <- liftEffect $ WS.send ws "message"
-- |
-- | -- Close connection
-- | liftEffect $ WS.close ws
-- | ```
-- |
-- | Based on spec 44-FFI-BINDINGS.md
module Sidepanel.FFI.WebSocket where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, makeAff)
import Data.Either (Either)

-- | Opaque WebSocket type
foreign import data WebSocketConnection :: Type

-- | Connection state
data ReadyState
  = Connecting  -- 0
  | Open        -- 1
  | Closing     -- 2
  | Closed      -- 3

derive instance eqReadyState :: Eq ReadyState

-- | Create WebSocket connection
foreign import create :: String -> Effect WebSocketConnection

-- | Get ready state
foreign import readyState :: WebSocketConnection -> Effect Int

-- | Send message
foreign import send :: WebSocketConnection -> String -> Effect (Either String Unit)

-- | Close connection
foreign import close :: WebSocketConnection -> Effect Unit

-- | Close with code and reason
foreign import closeWith :: WebSocketConnection -> Int -> String -> Effect Unit

-- | Set onopen handler
foreign import onOpen :: WebSocketConnection -> Effect Unit -> Effect Unit

-- | Set onclose handler
foreign import onClose :: WebSocketConnection -> (Int -> String -> Effect Unit) -> Effect Unit

-- | Set onerror handler
foreign import onError :: WebSocketConnection -> (String -> Effect Unit) -> Effect Unit

-- | Set onmessage handler
foreign import onMessage :: WebSocketConnection -> (String -> Effect Unit) -> Effect Unit

-- | Convert ready state int to type
toReadyState :: Int -> ReadyState
toReadyState 0 = Connecting
toReadyState 1 = Open
toReadyState 2 = Closing
toReadyState _ = Closed
