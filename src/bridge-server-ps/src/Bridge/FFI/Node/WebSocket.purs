-- | Node.js WebSocket Server FFI bindings
-- | Based on ws library
module Bridge.FFI.Node.WebSocket where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either)

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

-- | Start server
foreign import start :: WebSocketServer -> Effect Unit

-- | Close server
foreign import close :: WebSocketServer -> Effect Unit

-- | HTTP Request type (for origin validation)
foreign import data HttpRequest :: Type

-- | Set connection handler (receives connection and request)
foreign import onConnection :: WebSocketServer -> (WebSocketConnection -> HttpRequest -> Effect Unit) -> Effect Unit

-- | Get request headers
foreign import getRequestHeaders :: HttpRequest -> Effect (Array { key :: String, value :: String })

-- | Send message to connection
foreign import send :: WebSocketConnection -> String -> Effect (Either String Unit)

-- | Close connection
foreign import closeConnection :: WebSocketConnection -> Int -> String -> Effect Unit

-- | Get ready state
foreign import readyState :: WebSocketConnection -> Effect Int

-- | Set on message handler
foreign import onMessage :: WebSocketConnection -> (String -> Effect Unit) -> Effect Unit

-- | Set on close handler
foreign import onClose :: WebSocketConnection -> (Int -> String -> Effect Unit) -> Effect Unit

-- | Set on error handler
foreign import onError :: WebSocketConnection -> (String -> Effect Unit) -> Effect Unit

-- | Ping connection
foreign import ping :: WebSocketConnection -> String -> Effect Unit
