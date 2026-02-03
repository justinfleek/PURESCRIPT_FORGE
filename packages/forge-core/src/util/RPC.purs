-- | RPC utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/util/rpc.ts
module Forge.Util.RPC where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

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
