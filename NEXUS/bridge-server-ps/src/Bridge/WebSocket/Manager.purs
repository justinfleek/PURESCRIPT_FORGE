-- | WebSocket Manager - Connection Management
module Bridge.WebSocket.Manager where

import Prelude
import Effect (Effect)
import Effect.Ref (Ref, new, read, write, modify)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Bridge.FFI.Node.WebSocket as WS
import Bridge.FFI.Node.Pino as Pino
import Bridge.State.Store (StateStore)
import Bridge.FFI.Node.Express (HttpServer)
import Bridge.WebSocket.Handlers (handleJsonRpcMessage)

-- | Client connection
type ClientConnection =
  { id :: String
  , ws :: WS.WebSocketConnection
  }

-- | WebSocket Manager
type WebSocketManager =
  { server :: WS.WebSocketServer
  , clients :: Ref (Map String ClientConnection)
  , store :: StateStore
  , logger :: Pino.Logger
  , handlerMap :: Ref (Map String (String -> Effect String))
  }

-- | Create WebSocket manager
createManager :: HttpServer -> StateStore -> Pino.Logger -> Effect WebSocketManager
createManager httpServer store logger = do
  let options = { server: httpServer, path: "/ws" }
  wsServer <- WS.createServer options
  clientsRef <- new Map.empty
  handlerMapRef <- new Map.empty
  
  let manager = { server: wsServer, clients: clientsRef, store: store, logger: logger, handlerMap: handlerMapRef }
  
  WS.onConnection wsServer \conn -> do
    clientId <- generateClientId
    modify clientsRef (Map.insert clientId { id: clientId, ws: conn })
    Pino.info logger ("Client connected: " <> clientId)
    
    WS.onMessage conn \message -> do
      response <- handleJsonRpcMessage manager message
      WS.send conn response
    
    WS.onClose conn \code reason -> do
      modify clientsRef (Map.delete clientId)
      Pino.info logger ("Client disconnected: " <> clientId)
    
    WS.onError conn \error -> do
      Pino.error logger ("WebSocket error: " <> error)
  
  pure manager

-- | Register handler
registerHandler :: WebSocketManager -> String -> (String -> Effect String) -> Effect Unit
registerHandler manager method handler = do
  modify manager.handlerMap (Map.insert method handler)

-- | Broadcast message
broadcast :: WebSocketManager -> String -> Effect Unit
broadcast manager message = do
  clients <- read manager.clients
  Map.values clients # mapM_ \client -> do
    WS.send client.ws message

-- | Handle incoming message
handleMessage :: WebSocketManager -> String -> Effect Unit
handleMessage manager message = do
  handlerMap <- read manager.handlerMap
  -- Parse JSON-RPC and route - will be implemented in Handlers module
  pure unit

-- | Generate client ID
foreign import generateClientId :: Effect String
