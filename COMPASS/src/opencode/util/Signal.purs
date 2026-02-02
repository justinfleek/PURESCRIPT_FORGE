-- | Signal utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/util/signal.ts
module Opencode.Util.Signal where

import Prelude
import Effect (Effect)
import Opencode.Util.NotImplemented (notImplemented)

-- | Signal type (reactive value)
type Signal a =
  { get :: Effect a
  , set :: a -> Effect Unit
  , subscribe :: (a -> Effect Unit) -> Effect (Effect Unit)
  }

-- | Create a signal with initial value
create :: forall a. a -> Effect (Signal a)
create initial = notImplemented "Util.Signal.create"

-- | Create a computed signal
computed :: forall a b. Signal a -> (a -> b) -> Effect (Signal b)
computed source f = notImplemented "Util.Signal.computed"
