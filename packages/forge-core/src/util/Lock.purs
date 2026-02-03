-- | Lock utilities for mutual exclusion
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/util/lock.ts
module Forge.Util.Lock where

import Prelude
import Effect.Aff (Aff)
import Forge.Util.NotImplemented (notImplemented)

-- | Lock type
type Lock =
  { acquire :: Aff Unit
  , release :: Aff Unit
  }

-- | Create a new lock
create :: Aff Lock
create = notImplemented "Util.Lock.create"

-- | Run with lock
withLock :: forall a. Lock -> Aff a -> Aff a
withLock lock action = notImplemented "Util.Lock.withLock"
