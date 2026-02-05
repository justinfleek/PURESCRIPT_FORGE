-- | ID Generation
module Opencode.Id.Id where

import Prelude
import Effect (Effect)
import Data.String as String

-- | Generate a unique ID (UUID v4 format)
generate :: Effect String
generate = generateUUID
  where
    foreign import generateUUID :: Effect String

-- | Generate a short ID (base62, 8 characters)
generateShort :: Effect String
generateShort = generateShortId
  where
    foreign import generateShortId :: Effect String

-- | Validate an ID
-- | Checks that ID is non-empty and contains only valid characters
isValid :: String -> Boolean
isValid id =
  not (String.null id) &&
  String.length id >= 1 &&
  String.length id <= 128 &&
  String.all isValidChar id
  where
    isValidChar :: Char -> Boolean
    isValidChar c =
      (c >= 'a' && c <= 'z') ||
      (c >= 'A' && c <= 'Z') ||
      (c >= '0' && c <= '9') ||
      c == '-' ||
      c == '_'
