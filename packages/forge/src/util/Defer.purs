-- | Deferred execution utilities (Symbol.dispose pattern)
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/defer.ts
module Forge.Util.Defer
  ( Disposable
  , AsyncDisposable
  , defer
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)

-- | Sync disposable resource
type Disposable =
  { dispose :: Effect Unit
  }

-- | Async disposable resource
type AsyncDisposable =
  { asyncDispose :: Aff Unit
  }

-- | Create a defer wrapper for cleanup functions
-- | Returns a disposable that calls the function on dispose
foreign import defer :: (Unit -> Effect Unit) -> Disposable
