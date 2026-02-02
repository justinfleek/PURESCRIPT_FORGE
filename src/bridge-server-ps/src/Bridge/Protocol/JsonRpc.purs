-- | JSON-RPC Protocol Types and Handlers
module Bridge.Protocol.JsonRpc where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Argonaut (Json)
import Effect (Effect)

-- | JSON-RPC Request
type JsonRpcRequest =
  { jsonrpc :: String
  , method :: String
  , params :: Maybe Json
  , id :: Maybe String
  }

-- | JSON-RPC Response
type JsonRpcResponse =
  { jsonrpc :: String
  , result :: Maybe Json
  , error :: Maybe JsonRpcError
  , id :: Maybe String
  }

-- | JSON-RPC Error
type JsonRpcError =
  { code :: Int
  , message :: String
  , errorData :: Maybe Json
  }

-- | Parse JSON-RPC request
parseRequest :: String -> Either String JsonRpcRequest
parseRequest _ = Left "Not implemented"

-- | Create success response
successResponse :: Maybe String -> Json -> JsonRpcResponse
successResponse id result = 
  { jsonrpc: "2.0"
  , result: Just result
  , error: Nothing
  , id
  }

-- | Create error response  
errorResponse :: Maybe String -> Int -> String -> JsonRpcResponse
errorResponse id code message =
  { jsonrpc: "2.0"
  , result: Nothing
  , error: Just { code, message, errorData: Nothing }
  , id
  }

-- | Handle request (stub)
handleRequest :: JsonRpcRequest -> Effect Unit
handleRequest _ = pure unit
