-- | Bridge Server - HTTP/WebSocket Server Setup
module Bridge.Server where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, delay, launchAff_)
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds(..))
import Bridge.Config (Config)
import Bridge.State.Store (StateStore)
import Bridge.FFI.Node.Express as Express
import Bridge.FFI.Node.Pino as Pino
import Bridge.FFI.Haskell.Database as HaskellDB
import Bridge.FFI.Haskell.Analytics as DuckDB
import Bridge.WebSocket.Manager as WSManager
import Bridge.Venice.Client as Venice
import Bridge.Lean.Proxy as Lean
import Bridge.Notifications.Service as Notifications
import Bridge.Database.Sync as Sync

-- | FFI declarations (top-level)
foreign import encodeHandlerContext :: {} -> String
foreign import subscribeStateChanges :: StateStore -> WSManager.WebSocketManager -> Effect Unit
foreign import setNEXUSWebSocketManager :: WSManager.WebSocketManager -> Effect Unit

-- | Start the bridge server
startServer :: Config -> StateStore -> Pino.Logger -> Aff Unit
startServer config store logger = do
  -- Create Express app
  app <- liftEffect $ Express.createApp

  -- Health endpoint
  liftEffect $ Express.get app "/health" \_ res ->
    Express.sendJson res "{\"status\":\"ok\"}"

  -- Static file serving
  liftEffect $ Express.useStatic app config.staticDir

  -- Create HTTP server
  httpServer <- liftEffect $ Express.createServer app

  -- Create WebSocket manager
  wsManager <- liftEffect $ WSManager.createManager httpServer store logger

  -- Open databases
  db <- HaskellDB.openDatabase config.storage.path
  duckdb <- DuckDB.openAnalytics (Just config.storage.analyticsPath)

  -- Create Venice client (optional - depends on API key)
  veniceClient <- case config.venice.apiKey of
    Just apiKey -> do
      client <- liftEffect $ Venice.createVeniceClient apiKey store logger
      pure (Just client)
    Nothing -> do
      liftEffect $ Pino.warn logger "No Venice API key configured"
      pure Nothing

  -- Create Lean proxy (optional - depends on configuration)
  leanProxy <- if config.lean.enabled then do
    proxy <- liftEffect $ Lean.createLeanProxy store logger
    pure (Just proxy)
  else
    pure Nothing

  -- Create notification service
  notificationService <- liftEffect $ Notifications.create wsManager logger

  -- Subscribe to state changes for broadcasting
  liftEffect $ subscribeStateChanges store wsManager

  -- Set NEXUS WebSocket manager
  liftEffect $ setNEXUSWebSocketManager wsManager

  -- Start periodic sync
  launchAff_ $ Sync.startPeriodicSync db duckdb config.storage.syncIntervalMinutes logger

  -- Start listening
  liftEffect $ Express.listen httpServer config.port config.host do
    Pino.info logger ("Bridge server listening on " <> config.host <> ":" <> show config.port)

  -- Keep alive
  delay (Milliseconds 999999999.0)
