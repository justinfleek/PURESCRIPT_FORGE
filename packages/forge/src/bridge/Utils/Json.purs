-- | JSON Utilities
module Bridge.Utils.Json where

import Prelude
import Effect (Effect)
import Data.Either (Either)
import Data.Maybe (Maybe)
import Data.Array (all)
import Foreign (Foreign)

-- | FFI for safe JSON parsing
foreign import parseJson :: String -> Effect (Either String Foreign)

-- | FFI for field existence check
foreign import hasField :: Foreign -> String -> Boolean

-- | FFI for field extraction
foreign import getField :: Foreign -> String -> Maybe String

-- | Safe JSON parse
safeParseJson :: String -> Effect (Either String Foreign)
safeParseJson = parseJson

-- | Validate that a JSON object has all required fields
validateJsonStructure :: Foreign -> Array String -> Boolean
validateJsonStructure obj fields = all (hasField obj) fields

-- | Extract a string field from a JSON object
extractField :: Foreign -> String -> Maybe String
extractField = getField
