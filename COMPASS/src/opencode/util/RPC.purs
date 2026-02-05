-- | RPC utilities
module Opencode.Util.RPC where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))

-- | RPC request
type RPCRequest =
  { method :: String
  , params :: String  -- JSON
  , id :: String
  }

-- | RPC response
type RPCResponse =
  { result :: String  -- JSON
  , error :: String
  , id :: String
  }

-- | Call an RPC method
call :: String -> RPCRequest -> Aff (Either String RPCResponse)
call endpoint request = callRPC endpoint request

foreign import callRPC :: String -> RPCRequest -> Aff (Either String RPCResponse)
