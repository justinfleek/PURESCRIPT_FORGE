{-|
Module      : Bridge.WebSocket.Handlers.Types
Description : Type definitions for WebSocket JSON-RPC handlers
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Handler Types

Core type definitions for the JSON-RPC 2.0 WebSocket handlers,
including request/response structures and handler context.

== JSON-RPC 2.0 Protocol

Request: { jsonrpc: "2.0", id: Maybe, method: String, params: Maybe String }
Response: { jsonrpc: "2.0", id: Maybe, result: Maybe String, error: Maybe JsonRpcError }

== Standard Error Codes

| Code   | Meaning          |
|--------|------------------|
| -32700 | Parse error      |
| -32600 | Invalid Request  |
| -32601 | Method not found |
| -32602 | Invalid params   |
| -32603 | Internal error   |
-}
module Bridge.WebSocket.Handlers.Types
  ( -- * Handler Context
    HandlerContext(..)
    -- * JSON-RPC Types
  , JsonRpcRequest(..)
  , JsonRpcResponse(..)
  , JsonRpcError(..)
    -- * Response Helpers
  , successResponse
  , errorResponse
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

import Bridge.State.Store (StateStore)
import Bridge.Venice.Client (VeniceClient)
import Bridge.Lean.Proxy (LeanProxy)
import Bridge.FFI.Haskell.Database as DB
import Bridge.FFI.Haskell.Analytics as DuckDB
import Bridge.Notifications.Service (NotificationService)

-- ============================================================================
-- HANDLER CONTEXT
-- ============================================================================

{-| Handler context - Context passed to all JSON-RPC handlers.

Contains all dependencies and services needed by handler functions.

Invariants:
- db and duckdb are always available (initialized at server startup)
- veniceClient and leanProxy are optional (depend on configuration)
-}
type HandlerContext =
  { store :: StateStore
  , veniceClient :: Maybe VeniceClient
  , leanProxy :: Maybe LeanProxy
  , db :: DB.DatabaseHandle
  , duckdb :: DuckDB.AnalyticsHandle
  , notificationService :: NotificationService
  }

-- ============================================================================
-- JSON-RPC REQUEST
-- ============================================================================

{-| JSON-RPC request - JSON-RPC 2.0 request structure.

Fields:
- jsonrpc: Protocol version (must be "2.0")
- id: Optional request ID (String or Int) for matching responses
- method: Method name (e.g., "venice.chat", "lean.check")
- params: Optional JSON string containing method parameters
-}
type JsonRpcRequest =
  { jsonrpc :: String
  , id :: Maybe (Either String Int)
  , method :: String
  , params :: Maybe String -- JSON string
  }

-- ============================================================================
-- JSON-RPC RESPONSE
-- ============================================================================

{-| JSON-RPC response - JSON-RPC 2.0 response structure.

Invariants:
- Exactly one of result or error must be present (not both, not neither)
- id must match the request ID (or be Nothing for notifications)
- jsonrpc must be "2.0"
-}
type JsonRpcResponse =
  { jsonrpc :: String
  , id :: Maybe (Either String Int)
  , result :: Maybe String -- JSON string
  , error :: Maybe JsonRpcError
  }

{-| JSON-RPC error - Error object in JSON-RPC response.

Fields:
- code: Error code (negative for standard JSON-RPC, positive for custom)
- message: Human-readable error message
- data: Optional additional error data (JSON string)
-}
type JsonRpcError =
  { code :: Int
  , message :: String
  , data :: Maybe String
  }

-- ============================================================================
-- RESPONSE HELPERS
-- ============================================================================

{-| Create JSON-RPC success response. -}
successResponse :: Maybe (Either String Int) -> String -> JsonRpcResponse
successResponse id result =
  { jsonrpc: "2.0"
  , id
  , result: Just result
  , error: Nothing
  }

{-| Create JSON-RPC error response. -}
errorResponse :: Maybe (Either String Int) -> Int -> String -> Maybe String -> JsonRpcResponse
errorResponse id code message data_ =
  { jsonrpc: "2.0"
  , id
  , result: Nothing
  , error: Just { code, message, data: data_ }
  }
