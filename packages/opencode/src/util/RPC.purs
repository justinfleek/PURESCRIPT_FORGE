-- | RPC utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/util/rpc.ts
module Opencode.Util.RPC where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

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
call endpoint request = notImplemented "Util.RPC.call"
