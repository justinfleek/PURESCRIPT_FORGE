-- | Node.js WebSocket Server FFI bindings
-- | Based on ws library
module Bridge.FFI.Node.WebSocket where

import Prelude
import Effect (Effect)
import Bridge.FFI.Node.Express (HttpServer)

-- | Opaque WebSocket Server type
foreign import data WebSocketServer :: Type

-- | Opaque WebSocket Connection type
foreign import data WebSocketConnection :: Type

-- | Server options
type ServerOptions =
  { server :: HttpServer
  , path :: String
  }

-- | Create WebSocket server attached to HTTP server
foreign import createServer :: ServerOptions -> Effect WebSocketServer

-- | Set connection handler
foreign import onConnection :: WebSocketServer -> (WebSocketConnection -> Effect Unit) -> Effect Unit

-- | Send message to connection
foreign import send :: WebSocketConnection -> String -> Effect Unit

-- | Set on message handler
foreign import onMessage :: WebSocketConnection -> (String -> Effect Unit) -> Effect Unit

-- | Set on close handler
foreign import onClose :: WebSocketConnection -> (Int -> String -> Effect Unit) -> Effect Unit

-- | Set on error handler
foreign import onError :: WebSocketConnection -> (String -> Effect Unit) -> Effect Unit

-- | Close connection
foreign import closeConnection :: WebSocketConnection -> Int -> String -> Effect Unit
