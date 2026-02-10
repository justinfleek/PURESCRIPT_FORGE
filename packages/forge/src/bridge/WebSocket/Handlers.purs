-- | WebSocket JSON-RPC 2.0 Request Routing
module Bridge.WebSocket.Handlers
  ( module Bridge.WebSocket.Handlers.Types
  , handleRequest
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Maybe (Maybe(..))
import Bridge.WebSocket.Handlers.Types
import Bridge.WebSocket.Handlers.Venice as Venice
import Bridge.WebSocket.Handlers.Lean as Lean
import Bridge.WebSocket.Handlers.Session as Session
import Bridge.WebSocket.Handlers.Files as Files
import Bridge.WebSocket.Handlers.Auth as Auth

-- | Main JSON-RPC request router
handleRequest :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handleRequest ctx request =
  case request.method of
    -- State
    "state.get" -> Session.handleStateGet ctx request.params

    -- OpenCode
    "opencode.event" -> Auth.handleOpenCodeEventMessage ctx request.params

    -- Venice AI
    "venice.chat" -> Venice.handleVeniceChat ctx request.params
    "venice.models" -> Venice.handleVeniceModels ctx request.params
    "venice.image" -> Venice.handleVeniceImage ctx request.params

    -- Notifications
    "notification.dismiss" -> Auth.handleNotificationDismiss ctx request.params
    "notification.dismissAll" -> Auth.handleNotificationDismissAll ctx request.params

    -- Snapshots
    "snapshot.save" -> Session.handleSnapshotSave ctx request.params
    "snapshot.restore" -> Session.handleSnapshotRestore ctx request.params
    "snapshot.list" -> Session.handleSnapshotList ctx request.params
    "snapshot.get" -> Session.handleSnapshotGet ctx request.params

    -- Sessions
    "session.export" -> Session.handleSessionExport ctx request.params
    "session.new" -> Session.handleSessionNew ctx request.params

    -- Lean4
    "lean.check" -> Lean.handleLeanCheck ctx request.params
    "lean.goals" -> Lean.handleLeanGoals ctx request.params
    "lean.applyTactic" -> Lean.handleLeanApplyTactic ctx request.params
    "lean.searchTheorems" -> Lean.handleLeanSearchTheorems ctx request.params

    -- Files
    "file.context.add" -> Files.handleFileContextAdd ctx request.params
    "file.context.list" -> Files.handleFileContextList ctx request.params
    "file.read" -> Files.handleFileRead ctx request.params

    -- Terminal
    "terminal.execute" -> Files.handleTerminalExecute ctx request.params

    -- Web Search
    "web.search" -> Files.handleWebSearch ctx request.params

    -- Settings & Alerts
    "alerts.configure" -> Auth.handleAlertsConfigure ctx request
    "settings.save" -> Auth.handleSettingsSave ctx request.params

    -- Auth
    "auth.request" -> Auth.handleAuthRequest ctx request
    "auth.validate" -> Auth.handleAuthValidate ctx request

    -- Heartbeat
    "ping" -> Auth.handlePing ctx request
    "pong" -> Auth.handlePong ctx request

    -- Unknown method
    _ -> pure $ errorResponse request.id 4001 "Unknown method" Nothing
