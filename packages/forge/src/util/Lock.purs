-- | Lock utilities for mutual exclusion (Reader-Writer locks)
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/lock.ts
module Forge.Util.Lock
  ( Disposable
  , read
  , write
  ) where

import Prelude
import Effect.Aff (Aff)
import Effect (Effect)

-- | Disposable resource with dispose function
type Disposable =
  { dispose :: Effect Unit
  }

-- | Acquire a read lock (multiple readers allowed)
foreign import read :: String -> Aff Disposable

-- | Acquire a write lock (exclusive access)
foreign import write :: String -> Aff Disposable
