-- | RPC utilities (Web Worker communication)
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/rpc.ts
module Forge.Util.RPC
  ( RpcClient
  , listen
  , emit
  , client
  , call
  , on
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Foreign (Foreign)

-- | RPC client for worker communication
type RpcClient =
  { call :: String -> Foreign -> Aff Foreign
  , on :: String -> (Foreign -> Effect Unit) -> Effect (Effect Unit)
  }

-- | Listen for RPC calls in a worker
foreign import listen :: forall r. { | r } -> Effect Unit

-- | Emit an event from worker
foreign import emit :: String -> Foreign -> Effect Unit

-- | Create an RPC client for a target (Worker)
foreign import client :: Foreign -> RpcClient

-- | Call an RPC method
foreign import call :: RpcClient -> String -> Foreign -> Aff Foreign

-- | Subscribe to an RPC event
foreign import on :: RpcClient -> String -> (Foreign -> Effect Unit) -> Effect (Effect Unit)
