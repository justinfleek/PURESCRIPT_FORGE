-- | WebSocket Manager - Connection Management and Broadcasting
module Bridge.WebSocket.Manager where

import Prelude
import Effect (Effect)
import Effect.Ref (Ref, new)
import Data.Map (Map)
import Data.Map as Map
import Bridge.FFI.Node.WebSocket as WS
import Bridge.FFI.Node.Pino as Pino
import Bridge.State.Store (StateStore)
import Bridge.FFI.Node.Http (HttpServer)

-- | Client connection
type ClientConnection =
  { id :: String
  , ws :: WS.WebSocketConnection
  , isAuthenticated :: Boolean
  , lastPing :: Int
  }

-- | WebSocket Manager
type WebSocketManager =
  { server :: WS.WebSocketServer
  , clients :: Ref (Map String ClientConnection)
  , store :: StateStore
  , logger :: Pino.Logger
  }

-- | FFI declarations (top-level)
foreign import setHandlerContext :: WebSocketManager -> String -> Effect Unit
foreign import broadcast :: WebSocketManager -> String -> Effect Unit
foreign import handleMessage :: Pino.Logger -> StateStore -> String -> WS.WebSocketConnection -> Effect Unit

-- | Create WebSocket manager
createManager :: HttpServer -> StateStore -> Pino.Logger -> Effect WebSocketManager
createManager httpServer store logger = do
  wss <- WS.createServer
    { server: httpServer
    , path: "/ws"
    }
  clients <- new Map.empty
  WS.onConnection wss \ws req -> do
    _headers <- WS.getRequestHeaders req
    Pino.info logger "New WebSocket connection"
    WS.onMessage ws \message ->
      handleMessage logger store message ws
    WS.onClose ws \code reason ->
      Pino.info logger ("WebSocket closed: " <> show code <> " " <> reason)
    WS.onError ws \err ->
      Pino.error logger ("WebSocket error: " <> err)
  pure { server: wss, clients, store, logger }
