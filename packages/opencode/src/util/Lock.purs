-- | Lock utilities for mutual exclusion
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/util/lock.ts
module Opencode.Util.Lock where

import Prelude
import Effect.Aff (Aff)
import Opencode.Util.NotImplemented (notImplemented)

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
