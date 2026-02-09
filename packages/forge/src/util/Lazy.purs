-- | Lazy evaluation utilities
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/lazy.ts
module Forge.Util.Lazy
  ( LazyValue
  , lazy
  , reset
  ) where

import Prelude
import Effect (Effect)

-- | Lazy value type with reset capability
type LazyValue a =
  { get :: Effect a
  , reset :: Effect Unit
  }

-- | Create a lazy value from a thunk
foreign import lazy :: forall a. (Unit -> a) -> LazyValue a

-- | Reset a lazy value to re-evaluate on next access
foreign import reset :: forall a. LazyValue a -> Effect Unit
