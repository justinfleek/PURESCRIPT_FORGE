-- | Bridge validation utilities
module Forge.Bridge.Utils.Validation where

import Prelude
import Data.String (length)

-- | Validate that a number is non-negative
validateNonNegative :: Number -> Boolean
validateNonNegative n = n >= 0.0

-- | Validate that a number is positive
validatePositive :: Number -> Boolean
validatePositive n = n > 0.0

-- | Validate that a string is non-empty
validateNonEmpty :: String -> Boolean
validateNonEmpty s = length s > 0

-- | Validate that a number is within a range
validateRange :: Number -> Number -> Number -> Boolean
validateRange min max n = n >= min && n <= max
