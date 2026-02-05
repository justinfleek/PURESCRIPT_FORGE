-- | Bridge Server Implementation - HTTP and WebSocket Server Setup
-- | NEXUS-specific server initialization
module Bridge.Server where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, launchAff_, delay, Milliseconds(..))
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..))
import Bridge.Config (Config)
import Bridge.State.Store (StateStore, createStore)
import Bridge.FFI.Node.Express as Express
import Bridge.FFI.Node.Pino as Pino
import Bridge.WebSocket.Manager (createManager, WebSocketManager)
import Bridge.WebSocket.Handlers (registerNexusHandlers)
import Bridge.NEXUS.Postgres as Postgres
import Bridge.NEXUS.Postgres.FFI as PostgresFFI

-- | Start server - Initialize and start Bridge Server
startServer :: Config -> StateStore -> Pino.Logger -> Aff Unit
startServer config store logger = do
  liftEffect $ Pino.info logger "Initializing Nexus Bridge Server"
  
  -- Initialize PostgreSQL pool
  liftEffect $ case config.databaseUrl of
    Just url -> do
      PostgresFFI.initPostgresPoolFromUrl url
      Pino.info logger "PostgreSQL pool initialized from DATABASE_URL"
    Nothing -> do
      PostgresFFI.initPostgresPool
      Pino.info logger "PostgreSQL pool initialized from environment"
  
  -- Create HTTP server
  app <- liftEffect Express.createApp
  
  -- Health check endpoint
  liftEffect $ Express.get app "/health" \req res -> do
    Pino.info logger "Health check"
    Express.sendJson res """{"status":"ok"}"""
  
  -- Static files (if needed)
  liftEffect $ Express.useStatic app config.staticDir
  
  -- SPA fallback
  liftEffect $ Express.get app "*" \req res -> do
    Express.status res 404
    Express.sendJson res """{"error":"Not found"}"""
  
  -- Create HTTP server
  httpServer <- liftEffect $ Express.createServer app
  
  -- Create WebSocket manager (attached to HTTP server)
  wsManager <- liftEffect $ createManager httpServer store logger
  
  -- Register all NEXUS handlers
  liftEffect $ registerNexusHandlers wsManager
  liftEffect $ Pino.info logger "NEXUS handlers registered"
  
  -- Start HTTP server
  liftEffect $ Express.listen httpServer config.port config.host do
    Pino.info logger ("Nexus Bridge Server started on " <> config.host <> ":" <> show config.port)
    Pino.info logger ("WebSocket endpoint: ws://" <> config.host <> ":" <> show config.port <> "/ws")
    Pino.info logger ("Region: " <> config.region)
  
  -- Keep server running (delay indefinitely)
  delay (Milliseconds 999999999.0)
