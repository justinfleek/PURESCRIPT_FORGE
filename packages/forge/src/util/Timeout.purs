-- | Timeout utilities
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/timeout.ts
module Forge.Util.Timeout
  ( withTimeout
  , TimeoutError(..)
  ) where

import Prelude
import Effect.Aff (Aff)
import Effect.Exception (Error)

-- | Timeout error
newtype TimeoutError = TimeoutError String

-- | Run an action with timeout (throws on timeout)
foreign import withTimeout :: forall a. Int -> Aff a -> Aff a
