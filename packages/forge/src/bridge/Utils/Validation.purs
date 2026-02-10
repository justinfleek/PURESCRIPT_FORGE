-- | Bridge Validation Utilities
module Bridge.Utils.Validation where

import Prelude
import Data.Maybe (Maybe(..))

-- | FFI for string length
foreign import length :: String -> Int

-- | FFI for substring check
foreign import contains :: String -> String -> Boolean

-- | Validate that a number is non-negative
validateNonNegative :: Number -> Boolean
validateNonNegative n = n >= 0.0

-- | Validate that a number is positive
validatePositive :: Number -> Boolean
validatePositive n = n > 0.0

-- | Validate that a number is within a range
validateRange :: Number -> Number -> Number -> Boolean
validateRange minVal maxVal n = n >= minVal && n <= maxVal

-- | Validate that a string is non-empty
validateNonEmpty :: String -> Boolean
validateNonEmpty s = length s > 0

-- | Validate string length is within bounds
validateLength :: Int -> Int -> String -> Boolean
validateLength minLen maxLen s =
  let len = length s
  in len >= minLen && len <= maxLen

-- | Validate session ID format
validateSessionId :: String -> Boolean
validateSessionId s =
  validateNonEmpty s
  && validateLength 1 200 s
  && not (contains s " ")

-- | Validate JSON-RPC version
validateJsonRpcVersion :: String -> Boolean
validateJsonRpcVersion s = s == "2.0"

-- | Validate method name format
validateMethodName :: String -> Boolean
validateMethodName s =
  validateNonEmpty s
  && validateLength 1 100 s
  && not (contains s " ")

-- | Validate ISO timestamp format (basic check)
validateTimestamp :: String -> Boolean
validateTimestamp s =
  validateNonEmpty s
  && contains s "T"
  && (contains s "Z" || contains s "+" || contains s "-")
