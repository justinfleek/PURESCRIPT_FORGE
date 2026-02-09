-- | Context utilities (AsyncLocalStorage pattern)
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/context.ts
module Forge.Util.Context
  ( Context
  , NotFoundError(..)
  , create
  , use
  , provide
  ) where

import Prelude
import Effect (Effect)
import Effect.Exception (Error)
import Foreign (Foreign)

-- | Context not found error
newtype NotFoundError = NotFoundError String

-- | Context type for AsyncLocalStorage-style scoping
type Context a =
  { use :: Effect a
  , provide :: forall r. a -> Effect r -> Effect r
  }

-- | Create a new context with a name
foreign import create :: forall a. String -> Context a

-- | Get value from context (throws NotFoundError if not set)
foreign import use :: forall a. Context a -> Effect a

-- | Run action with context value
foreign import provide :: forall a r. Context a -> a -> Effect r -> Effect r
