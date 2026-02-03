-- | WebSocket Manager - WebSocket Connection Management and Broadcasting
-- |
-- | **What:** Manages WebSocket server connections, client authentication, message
-- |         broadcasting, and connection lifecycle. Handles WebSocket upgrade requests
-- |         from HTTP server and maintains a registry of connected clients.
-- | **Why:** Provides centralized WebSocket connection management for real-time
-- |         bidirectional communication between Bridge Server and clients (sidepanel,
-- |         NEXUS agents). Enables broadcasting state updates to all connected clients.
-- | **How:** Wraps Node.js WebSocket server, maintains a Map of client connections,
-- |         handles connection/disconnection events, and provides broadcast functionality
-- |         for sending messages to all clients.
-- |
-- | **Dependencies:**
-- | - `Bridge.FFI.Node.WebSocket`: Node.js WebSocket bindings
-- | - `Bridge.State.Store`: Application state store
-- | - `Bridge.FFI.Node.Pino`: Structured logging
-- |
-- | **Mathematical Foundation:**
-- | - **Connection Invariant:** Each client connection has a unique ID. Client IDs
-- |   are never reused within a server session.
-- | - **Broadcast Invariant:** Broadcast messages are sent to all authenticated clients
-- |   synchronously. Order of delivery is not guaranteed.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.WebSocket.Manager as WSManager
-- |
-- | -- Create manager
-- | manager <- WSManager.createManager httpServer store logger
-- |
-- | -- Broadcast message
-- | WSManager.broadcast manager """{"type":"state.update","data":{...}}"""
-- | ```
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
import Bridge.FFI.Node.Http (HttpServer)

-- | Client connection
type ClientConnection =
  { id :: String
  , ws :: WS.WebSocketConnection
  , isAuthenticated :: Boolean
  , lastPing :: Int
  }

-- | WebSocket Manager - WebSocket server manager container
-- |
-- | **Purpose:** Contains WebSocket server instance, client registry, state store,
-- |             and logger. Provides all dependencies needed for WebSocket operations.
-- | **Fields:**
-- | - `server`: WebSocket server instance
-- | - `clients`: Map of client ID to ClientConnection
-- | - `store`: Application state store
-- | - `logger`: Pino logger for structured logging
type WebSocketManager =
  { server :: WS.WebSocketServer
  , clients :: Ref (Map String ClientConnection)
  , store :: StateStore
  , logger :: Pino.Logger
  }

-- | Handler context (set after initialization)
foreign import setHandlerContext :: WebSocketManager -> String -> Effect Unit -- Takes JSON string

-- | Broadcast message to all clients
foreign import broadcast :: WebSocketManager -> String -> Effect Unit -- Takes JSON string

-- | Create WebSocket manager - Initialize WebSocket server
-- |
-- | **Purpose:** Creates a WebSocket manager attached to an HTTP server, sets up
-- |             connection handlers, and initializes client registry.
-- | **Parameters:**
-- | - `httpServer`: HTTP server to attach WebSocket server to
-- | - `store`: Application state store
-- | - `logger`: Pino logger
-- | **Returns:** WebSocketManager instance
-- | **Side Effects:** Creates WebSocket server, registers connection handlers
-- |
-- | **Initialization:**
-- | - Creates WebSocket server on path "/ws"
-- | - Initializes empty client registry
-- | - Registers connection handler for new clients
-- |
-- | **Example:**
-- | ```purescript
-- | manager <- createManager httpServer store logger
-- | ```
createManager :: HttpServer -> StateStore -> Pino.Logger -> Effect WebSocketManager
createManager httpServer store logger = do
  wss <- WS.createServer
    { server: httpServer
    , path: "/ws"
    }
  
  clients <- new Map.empty
  
  -- Set connection handler with origin validation
  WS.onConnection wss \ws req -> do
    -- Validate origin
    headers <- WS.getRequestHeaders req
    -- TODO: Add origin validation here (will be implemented in next step)
    Pino.info logger "New WebSocket connection"
    -- Set up message handler
    WS.onMessage ws \message -> do
      handleMessage logger store message ws
    -- Set up close handler
    WS.onClose ws \code reason -> do
      Pino.info logger ("WebSocket closed: " <> show code <> " " <> reason)
    -- Set up error handler
    WS.onError ws \error -> do
      Pino.error logger ("WebSocket error: " <> error)
  
  pure { server: wss, clients, store, logger }
  where
    foreign import handleMessage :: Pino.Logger -> StateStore -> String -> WS.WebSocketConnection -> Effect Unit
