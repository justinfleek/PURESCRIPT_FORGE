-- | Signal utilities (promise-based signaling)
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/signal.ts
module Forge.Util.Signal
  ( Signal
  , create
  , trigger
  , wait
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)

-- | Signal type for one-shot synchronization
type Signal =
  { trigger :: Effect Unit
  , wait :: Aff Unit
  }

-- | Create a new signal
foreign import create :: Effect Signal

-- | Trigger the signal
foreign import trigger :: Signal -> Effect Unit

-- | Wait for the signal
foreign import wait :: Signal -> Aff Unit
