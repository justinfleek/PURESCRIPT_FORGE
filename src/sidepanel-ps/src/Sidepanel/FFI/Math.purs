-- | Math FFI Module - Math Utilities
-- |
-- | **What:** Provides FFI bindings for JavaScript Math functions.
-- | **Why:** PureScript doesn't have built-in random number generation.
-- | **How:** Uses foreign function imports to wrap JavaScript Math.random().
module Sidepanel.FFI.Math where

import Prelude
import Effect (Effect)

-- | Generate random number between 0 and 1
foreign import random :: Effect Number
