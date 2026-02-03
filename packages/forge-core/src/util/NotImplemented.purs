-- | NotImplemented utility for stub functions
module Forge.Util.NotImplemented where

import Prelude
import Effect.Exception (throw)
import Effect.Unsafe (unsafePerformEffect)

-- | Throw a not implemented error with a function name
-- | This is used in stubs to mark functions that need implementation
notImplemented :: forall a. String -> a
notImplemented fnName = unsafePerformEffect $ throw $ "Not implemented: " <> fnName
