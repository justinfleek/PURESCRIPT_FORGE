-- | Handler Types - Core type definitions for WebSocket JSON-RPC handlers
module Bridge.WebSocket.Handlers.Types
  ( HandlerContext
  , JsonRpcRequest
  , JsonRpcResponse
  , JsonRpcError
  , successResponse
  , errorResponse
  ) where

import Prelude
import Data.Either (Either)
import Data.Maybe (Maybe(..))
import Bridge.State.Store (StateStore)
import Bridge.Venice.Client (VeniceClient)
import Bridge.Lean.Proxy (LeanProxy)
import Bridge.FFI.Haskell.Database as DB
import Bridge.FFI.Haskell.Analytics as DuckDB
import Bridge.Notifications.Service (NotificationService)

-- | Handler context - Dependencies for all JSON-RPC handlers
type HandlerContext =
  { store :: StateStore
  , veniceClient :: Maybe VeniceClient
  , leanProxy :: Maybe LeanProxy
  , db :: DB.Database
  , duckdb :: DuckDB.AnalyticsDB
  , notificationService :: NotificationService
  }

-- | JSON-RPC 2.0 request
type JsonRpcRequest =
  { jsonrpc :: String
  , id :: Maybe (Either String Int)
  , method :: String
  , params :: Maybe String
  }

-- | JSON-RPC 2.0 response
type JsonRpcResponse =
  { jsonrpc :: String
  , id :: Maybe (Either String Int)
  , result :: Maybe String
  , error :: Maybe JsonRpcError
  }

-- | JSON-RPC error
type JsonRpcError =
  { code :: Int
  , message :: String
  , errData :: Maybe String
  }

-- | Create success response
successResponse :: Maybe (Either String Int) -> String -> JsonRpcResponse
successResponse reqId result =
  { jsonrpc: "2.0"
  , id: reqId
  , result: Just result
  , error: Nothing
  }

-- | Create error response
errorResponse :: Maybe (Either String Int) -> Int -> String -> Maybe String -> JsonRpcResponse
errorResponse reqId code message errData =
  { jsonrpc: "2.0"
  , id: reqId
  , result: Nothing
  , error: Just { code, message, errData }
  }
