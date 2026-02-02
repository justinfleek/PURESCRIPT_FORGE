-- | JSON Utilities
-- | JSON parsing and validation utilities
module Bridge.Utils.Json where

import Prelude
import Effect (Effect)
import Data.Either (Either(..))

-- | Safe JSON parse
safeParseJson :: String -> Effect (Either String {})
safeParseJson jsonStr = do
  result <- parseJson jsonStr
  pure result

-- | Validate JSON structure
validateJsonStructure :: {} -> Array String -> Boolean
validateJsonStructure json requiredFields = 
  foldl (\acc field -> acc && hasField json field) true requiredFields

-- | Extract field from JSON object
extractField :: {} -> String -> Maybe String
extractField json field = getField json field

foreign import parseJson :: String -> Effect (Either String {})
foreign import hasField :: {} -> String -> Boolean
foreign import getField :: {} -> String -> Maybe String
foreign import foldl :: forall a b. (b -> a -> b) -> b -> Array a -> b
