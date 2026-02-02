-- | JSON-RPC 2.0 Protocol Types
-- | Standard JSON-RPC 2.0 request/response types for WebSocket communication
module Bridge.Protocol.JsonRpc where

import Prelude
import Data.Argonaut (Json, class EncodeJson, class DecodeJson, encodeJson, decodeJson, (.:), (.:?))
import Data.Either (Either)
import Data.Maybe (Maybe)

-- | JSON-RPC Request
type JsonRpcRequest =
  { jsonrpc :: String
  , id :: Maybe (Either String Int)
  , method :: String
  , params :: Maybe String
  }

instance decodeJsonJsonRpcRequest :: DecodeJson JsonRpcRequest where
  decodeJson json = do
    obj <- decodeJson json
    jsonrpc <- obj .: "jsonrpc"
    id <- obj .:? "id"
    method <- obj .: "method"
    params <- obj .:? "params"
    pure { jsonrpc, id, method, params }

instance encodeJsonJsonRpcRequest :: EncodeJson JsonRpcRequest where
  encodeJson req = encodeJson
    { jsonrpc: req.jsonrpc
    , id: req.id
    , method: req.method
    , params: req.params
    }

-- | JSON-RPC Error
type JsonRpcError =
  { code :: Int
  , message :: String
  , data :: Maybe Json
  }

instance decodeJsonJsonRpcError :: DecodeJson JsonRpcError where
  decodeJson json = do
    obj <- decodeJson json
    code <- obj .: "code"
    message <- obj .: "message"
    data <- obj .:? "data"
    pure { code, message, data }

instance encodeJsonJsonRpcError :: EncodeJson JsonRpcError where
  encodeJson err = encodeJson
    { code: err.code
    , message: err.message
    , data: err.data
    }

-- | JSON-RPC Response
type JsonRpcResponse =
  { jsonrpc :: String
  , id :: Maybe (Either String Int)
  , result :: Maybe String
  , error :: Maybe JsonRpcError
  }

instance decodeJsonJsonRpcResponse :: DecodeJson JsonRpcResponse where
  decodeJson json = do
    obj <- decodeJson json
    jsonrpc <- obj .: "jsonrpc"
    id <- obj .:? "id"
    result <- obj .:? "result"
    error <- obj .:? "error"
    pure { jsonrpc, id, result, error }

instance encodeJsonJsonRpcResponse :: EncodeJson JsonRpcResponse where
  encodeJson resp = encodeJson
    { jsonrpc: resp.jsonrpc
    , id: resp.id
    , result: resp.result
    , error: resp.error
    }
