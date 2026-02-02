{-|
Module      : Bridge.WebSocket.Handlers
Description : JSON-RPC 2.0 Request Routing and Processing
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= WebSocket JSON-RPC Handlers

Implements all JSON-RPC 2.0 method handlers for WebSocket communication
between the Bridge Server and clients (sidepanel, NEXUS agents).

== Module Structure

The Handlers module is split into sub-modules for maintainability:

* "Bridge.WebSocket.Handlers.Types" - Core types (Context, Request, Response)
* "Bridge.WebSocket.Handlers.Venice" - Venice AI chat and image handlers
* "Bridge.WebSocket.Handlers.Lean" - Lean4 proof assistant handlers
* "Bridge.WebSocket.Handlers.Session" - Session and snapshot handlers
* "Bridge.WebSocket.Handlers.Files" - File context and terminal handlers
* "Bridge.WebSocket.Handlers.Auth" - Auth, settings, notifications, heartbeat

== Supported Methods

| Method               | Handler Module  | Description                    |
|----------------------|-----------------|--------------------------------|
| state.get            | Session         | Get current application state  |
| opencode.event       | Auth            | Handle OpenCode SDK event      |
| venice.chat          | Venice          | Venice AI chat                 |
| venice.models        | Venice          | List Venice models             |
| venice.image         | Venice          | Generate image                 |
| notification.*       | Auth            | Notification management        |
| snapshot.*           | Session         | Snapshot save/restore/list     |
| session.*            | Session         | Session management             |
| lean.*               | Lean            | Lean4 proof operations         |
| file.*               | Files           | File context management        |
| terminal.execute     | Files           | Terminal command execution     |
| web.search           | Files           | Web search                     |
| alerts.configure     | Auth            | Configure alerts               |
| settings.save        | Auth            | Save settings                  |
| auth.*               | Auth            | Authentication                 |
| ping/pong            | Auth            | Heartbeat                      |
| nexus.*              | NEXUS           | NEXUS agent operations         |

== Error Codes

| Code   | Meaning          |
|--------|------------------|
| -32700 | Parse error      |
| -32600 | Invalid Request  |
| -32601 | Method not found |
| -32602 | Invalid params   |
| -32603 | Internal error   |
| 4001   | Unknown method   |
| 4002   | Missing params   |
| 5001+  | Venice errors    |
| 6001+  | File errors      |
| 7001+  | Terminal errors  |
| 8001+  | Web search errors|
| 9001+  | Lean errors      |
-}
module Bridge.WebSocket.Handlers
  ( -- * Re-exports
    module Bridge.WebSocket.Handlers.Types
    -- * Main Router
  , handleRequest
  ) where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..))

import Bridge.WebSocket.Handlers.Types
import Bridge.WebSocket.Handlers.Venice as Venice
import Bridge.WebSocket.Handlers.Lean as Lean
import Bridge.WebSocket.Handlers.Session as Session
import Bridge.WebSocket.Handlers.Files as Files
import Bridge.WebSocket.Handlers.Auth as Auth
import Bridge.NEXUS.Handlers as NexusHandlers

-- ============================================================================
-- MAIN ROUTER
-- ============================================================================

{-| Handle JSON-RPC request - Main request router.

Routes incoming JSON-RPC requests to appropriate handler functions
based on method name. This is the entry point for all JSON-RPC requests.
-}
handleRequest :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handleRequest ctx request = do
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
    
    -- NEXUS Agent
    "nexus.agent.launch" -> liftEffect $ NexusHandlers.nexusAgentLaunch request
    "nexus.agent.status" -> liftEffect $ NexusHandlers.nexusAgentStatus request
    "nexus.agent.profile" -> liftEffect $ NexusHandlers.nexusAgentProfile request
    "nexus.attestation.create" -> liftEffect $ NexusHandlers.nexusAttestationCreate request
    
    -- Unknown
    _ -> pure $ errorResponse request.id 4001 "Unknown method" Nothing
