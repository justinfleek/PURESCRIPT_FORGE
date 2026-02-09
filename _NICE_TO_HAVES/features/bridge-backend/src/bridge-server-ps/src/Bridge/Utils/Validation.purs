-- | Validation Utilities
-- | Input validation and boundary checking
module Bridge.Utils.Validation where

import Prelude
import Data.Maybe (Maybe(..))

-- | Validate non-negative number
validateNonNegative :: Number -> Boolean
validateNonNegative n = n >= 0.0

-- | Validate positive number
validatePositive :: Number -> Boolean
validatePositive n = n > 0.0

-- | Validate number in range
validateRange :: Number -> Number -> Number -> Boolean
validateRange min max n = n >= min && n <= max

-- | Validate non-empty string
validateNonEmpty :: String -> Boolean
validateNonEmpty s = s /= ""

-- | Validate string length
validateLength :: Int -> Int -> String -> Boolean
validateLength min max s = 
  let len = length s
  in len >= min && len <= max

-- | Validate session ID format
validateSessionId :: String -> Boolean
validateSessionId id = 
  validateNonEmpty id && 
  validateLength 1 200 id &&
  not (contains " " id)

-- | Validate JSON-RPC version
validateJsonRpcVersion :: String -> Boolean
validateJsonRpcVersion version = version == "2.0"

-- | Validate JSON-RPC method name
validateMethodName :: String -> Boolean
validateMethodName method = 
  validateNonEmpty method &&
  validateLength 1 100 method &&
  not (contains " " method)

-- | Validate timestamp ISO format (basic check)
validateTimestamp :: String -> Boolean
validateTimestamp ts = 
  validateNonEmpty ts &&
  contains "T" ts &&
  (contains "Z" ts || contains "+" ts || contains "-" ts)

foreign import length :: String -> Int
foreign import contains :: String -> String -> Boolean
