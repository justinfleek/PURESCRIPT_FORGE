-- | Bridge Server Implementation - HTTP and WebSocket Server Setup
-- |
-- | **What:** Initializes and starts the Bridge Server, including HTTP server, WebSocket
-- |         manager, database connections, client integrations (Venice, OpenCode, Lean),
-- |         and state synchronization.
-- | **Why:** Provides the server-side infrastructure for the Bridge Server application,
-- |         coordinating all services and exposing them via HTTP and WebSocket endpoints.
-- | **How:** Sets up Express HTTP server with static file serving and SPA fallback,
-- |         creates WebSocket manager for real-time communication, initializes databases
-- |         (SQLite for persistence, DuckDB for analytics), creates client integrations,
-- |         and starts periodic database synchronization.
-- |
-- | **Dependencies:**
-- | - `Bridge.Config`: Server configuration (port, host, paths, API keys)
-- | - `Bridge.State.Store`: Application state store
-- | - `Bridge.WebSocket.Manager`: WebSocket connection management
-- | - `Bridge.Venice.Client`: Venice AI API client
-- | - `Bridge.Opencode.Client`: OpenCode SDK integration
-- | - `Bridge.Lean.Proxy`: Lean4 LSP proxy
-- | - `Bridge.FFI.Haskell.Database`: SQLite database operations
-- | - `Bridge.FFI.Haskell.Analytics`: DuckDB analytics operations
-- |
-- | **Mathematical Foundation:**
-- | - **Server Lifecycle:** Server runs indefinitely until process termination.
-- |   Uses `delay` with large timeout to keep Aff computation alive.
-- | - **State Synchronization:** State changes are broadcast to all connected WebSocket
-- |   clients via `subscribeStateChanges`. Ensures all clients have consistent state.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Server as Server
-- | import Bridge.Config as Config
-- | import Bridge.State.Store as Store
-- | import Bridge.FFI.Node.Pino as Pino
-- |
-- | main = launchAff_ do
-- |   config <- liftEffect Config.loadConfig
-- |   store <- liftEffect Store.createStore
-- |   logger <- liftEffect Pino.createLogger
-- |   Server.startServer config store logger
-- | ```
module Bridge.Server where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, launchAff_, delay, Milliseconds(..))
import Effect.Class (liftEffect)
import Effect.Ref (Ref, new, read, write)
import Data.Maybe (Maybe(..))
import Bridge.Config (Config)
import Bridge.State.Store (StateStore, createStore, setConnected)
import Bridge.FFI.Node.Express as Express
import Bridge.FFI.Node.WebSocket as WS
import Bridge.FFI.Node.Pino as Pino
import Bridge.FFI.Haskell.Database as DB
import Bridge.WebSocket.Handlers (HandlerContext)
import Bridge.WebSocket.Manager (createManager, WebSocketManager, setHandlerContext, broadcast)
import Bridge.Venice.Client (createVeniceClient, VeniceClient)
import Bridge.Opencode.Client (createOpencodeClient, OpencodeClient)
import Bridge.Lean.Proxy (createLeanProxy, LeanProxy)
import Bridge.Notifications.Service (create as createNotificationService, NotificationService)
import Bridge.Database.Sync (createSyncState, startPeriodicSync, SyncConfig)
import Bridge.FFI.Haskell.Analytics as DuckDB

-- | Start server - Initialize and start Bridge Server
-- |
-- | **Purpose:** Initializes all server components and starts the HTTP/WebSocket server.
-- | **Parameters:**
-- | - `config`: Server configuration (port, host, paths, API keys)
-- | - `store`: Application state store
-- | - `logger`: Pino logger for structured logging
-- | **Returns:** Aff computation that runs indefinitely
-- | **Side Effects:**
-- |             - Creates HTTP server on configured port/host
-- |             - Sets up WebSocket manager
-- |             - Opens database connections
-- |             - Creates client integrations
-- |             - Starts periodic database sync
-- |             - Registers state change listeners
-- |
-- | **Initialization Steps:**
-- | 1. Create Express HTTP server with health check and static file serving
-- | 2. Create WebSocket manager attached to HTTP server
-- | 3. Initialize SQLite database (persistence)
-- | 4. Initialize DuckDB database (analytics)
-- | 5. Start periodic sync (SQLite → DuckDB)
-- | 6. Create Venice client (if API key provided)
-- | 7. Create OpenCode client (if SDK available)
-- | 8. Create Lean proxy (if enabled)
-- | 9. Create notification service
-- | 10. Set WebSocket handler context
-- | 11. Register WebSocket manager with NEXUS
-- | 12. Subscribe to state changes for broadcasting
-- | 13. Start HTTP server
-- | 14. Set connected state to true
-- | 15. Keep server running (delay indefinitely)
-- |
-- | **Example:**
-- | ```purescript
-- | Server.startServer config store logger
-- | ```
startServer :: Config -> StateStore -> Pino.Logger -> Aff Unit
startServer config store logger = do
  liftEffect $ Pino.info logger "Initializing Bridge Server"
  
  -- Create HTTP server
  app <- liftEffect Express.createApp
  
  -- Health check endpoint
  liftEffect $ Express.get app "/health" \req res -> do
    Pino.info logger "Health check"
    Express.sendJson res """{"status":"ok"}"""
  
  -- Static files
  liftEffect $ Express.useStatic app config.staticDir
  
  -- SPA fallback
  liftEffect $ Express.get app "*" \req res -> do
    Express.sendFile res config.staticDir "index.html"
  
  -- Create HTTP server
  httpServer <- liftEffect $ Express.createServer app
  
  -- Create WebSocket manager (attached to HTTP server)
  wsManager <- liftEffect $ createManager httpServer store logger
  
  -- Initialize database
  db <- liftEffect $ DB.openDatabase config.storage.path
  liftEffect $ Pino.infoFields logger "Database initialized" """{"path":"\"""" <> config.storage.path <> "\"""}"""
  
  -- Initialize analytics database
  duckdb <- liftEffect $ DuckDB.openAnalytics (Just config.storage.analyticsPath)
  liftEffect $ Pino.infoFields logger "Analytics database initialized" """{"path":"\"""" <> config.storage.analyticsPath <> "\"""}"""
  
  -- Create sync state
  syncState <- liftEffect $ createSyncState
  
  -- Start periodic sync (SQLite → DuckDB)
  let syncConfig = 
        { intervalMinutes: config.storage.syncIntervalMinutes
        , sqlitePath: config.storage.path
        , duckdbPath: config.storage.analyticsPath
        }
  liftEffect $ startPeriodicSync syncConfig db duckdb logger syncState
  liftEffect $ Pino.info logger "Database sync started"
  
  -- Create Venice client (if API key available)
  veniceClient <- case config.venice.apiKey of
    Just apiKey -> do
      client <- liftEffect $ createVeniceClient apiKey store logger
      liftEffect $ Pino.info logger "Venice API client initialized"
      pure (Just client)
    Nothing -> do
      liftEffect $ Pino.warn logger "Venice API key not provided, balance tracking disabled"
      pure Nothing
  
  -- Create OpenCode client
  opencodeClient <- createOpencodeClient store config.opencode logger
  case opencodeClient of
    Just client -> liftEffect $ Pino.info logger "OpenCode client connected"
    Nothing -> liftEffect $ Pino.warn logger "OpenCode client not available (SDK may not be installed)"
  
  -- Create Lean proxy (if enabled)
  leanProxy <- if config.lean.enabled then do
    proxy <- liftEffect $ createLeanProxy store logger
    liftEffect $ Pino.info logger "Lean LSP proxy created"
    pure (Just proxy)
  else
    pure Nothing
  
  -- Create notification service
  notificationService <- liftEffect $ createNotificationService wsManager logger
  
  -- Set handler context for WebSocket manager
  liftEffect $ setHandlerContext wsManager (encodeHandlerContext
    { store
    , veniceClient
    , leanProxy
    , db
    , duckdb
    , notificationService
    })
  
  -- Register WebSocket manager with NEXUS
  liftEffect $ setNEXUSWebSocketManager wsManager
  
  -- Subscribe to state changes and broadcast to clients
  liftEffect $ subscribeStateChanges store wsManager
  
  -- Start HTTP server
  liftEffect $ Express.listen httpServer config.port config.host $ do
    Pino.infoFields logger "Bridge Server started" 
      ("""{"port":""" <> show config.port <> ""","host":"\"""" <> config.host <> "\"""}""")
  
  -- Set connected state
  liftEffect $ setConnected store true
  
  -- Keep server running
  delay (Milliseconds 999999999.0)

-- | Encode handler context - Serialize HandlerContext to JSON string
-- |
-- | **Purpose:** Converts HandlerContext (containing store, clients, databases) to JSON
-- |             string for WebSocket manager. Used internally by startServer.
-- | **Parameters:**
-- | - `context`: HandlerContext to encode
-- | **Returns:** JSON string representation
-- | **Side Effects:** None (pure serialization)
foreign import encodeHandlerContext :: HandlerContext -> String

-- | Subscribe to state changes - Register state change broadcaster
-- |
-- | **Purpose:** Subscribes to state store changes and broadcasts them to all connected
-- |             WebSocket clients. Ensures all clients have synchronized state.
-- | **Parameters:**
-- | - `store`: State store to subscribe to
-- | - `wsManager`: WebSocket manager for broadcasting
-- | **Returns:** Unit
-- | **Side Effects:** Registers listener that broadcasts state changes via WebSocket
foreign import subscribeStateChanges :: StateStore -> WebSocketManager -> Effect Unit

-- | Set NEXUS WebSocket manager - Register manager with NEXUS system
-- |
-- | **Purpose:** Registers the WebSocket manager with the NEXUS agent system, enabling
-- |             NEXUS agents to communicate via WebSocket.
-- | **Parameters:**
-- | - `wsManager`: WebSocket manager to register
-- | **Returns:** Unit
-- | **Side Effects:** Registers manager globally for NEXUS system access
foreign import setNEXUSWebSocketManager :: WebSocketManager -> Effect Unit