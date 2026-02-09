{-|
Module      : Forge.Id.Id
Description : Unique ID Generation

Utilities for generating unique identifiers using UUID v4 and
nanoid-style short IDs.

== ID Formats

| Type    | Length | Example                              |
|---------|--------|--------------------------------------|
| UUID    | 36     | 550e8400-e29b-41d4-a716-446655440000 |
| Short   | 21     | V1StGXR8_Z5jdHi6B-myT               |
| Nano    | 8      | xYz3Kp9q                             |
-}
module Forge.Id.Id
  ( -- * Generation
    generate
  , generateShort
  , generateNano
  , generatePrefixed
    -- * Validation
  , isValid
  , isValidUUID
  , isValidShort
    -- * Parsing
  , parseUUID
  , getTimestamp
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.Regex as Regex
import Data.String.Regex.Flags (noFlags)
import Data.Either (Either(..))
import Effect (Effect)

-- ============================================================================
-- FFI
-- ============================================================================

-- | Generate UUID v4
foreign import generateUUIDFFI :: Effect String

-- | Generate nanoid-style short ID
foreign import generateNanoidFFI :: Int -> Effect String

-- ============================================================================
-- GENERATION
-- ============================================================================

{-| Generate a unique UUID v4 identifier.

Format: xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx
-}
generate :: Effect String
generate = generateUUIDFFI

{-| Generate a short ID (21 characters).

Uses URL-safe alphabet: A-Za-z0-9_-
-}
generateShort :: Effect String
generateShort = generateNanoidFFI 21

{-| Generate a nano ID (8 characters).

Useful for user-facing IDs where brevity matters.
-}
generateNano :: Effect String
generateNano = generateNanoidFFI 8

{-| Generate an ID with a prefix.

Example: "session_xYz3Kp9q"
-}
generatePrefixed :: String -> Effect String
generatePrefixed prefix = do
  nano <- generateNano
  pure $ prefix <> "_" <> nano

-- ============================================================================
-- VALIDATION
-- ============================================================================

{-| Check if a string is a valid ID (UUID or short). -}
isValid :: String -> Boolean
isValid str = isValidUUID str || isValidShort str

{-| Check if a string is a valid UUID. -}
isValidUUID :: String -> Boolean
isValidUUID str =
  let uuidPattern = "^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$"
  in case Regex.regex uuidPattern (noFlags { ignoreCase = true }) of
    Left _ -> false
    Right rx -> Regex.test rx str

{-| Check if a string is a valid short ID. -}
isValidShort :: String -> Boolean
isValidShort str =
  let len = String.length str
      validChars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_-"
  in len >= 8 && len <= 21 && stringAll (\c -> String.contains (String.Pattern (String.singleton c)) validChars) str

-- ============================================================================
-- PARSING
-- ============================================================================

{-| Parse a UUID string, returning Nothing if invalid. -}
parseUUID :: String -> Maybe String
parseUUID str =
  if isValidUUID str
  then Just str
  else Nothing

{-| Extract timestamp from a UUID v1 (not applicable to v4).

For v4 UUIDs, this returns Nothing as they don't contain timestamps.
-}
getTimestamp :: String -> Maybe Number
getTimestamp _ = Nothing  -- UUID v4 doesn't have timestamp

-- ============================================================================
-- HELPERS
-- ============================================================================

-- Helper for String.all
stringAll :: (Char -> Boolean) -> String -> Boolean
stringAll pred str =
  let chars = String.toCodePointArray str
  in stringAllImpl pred chars

foreign import stringAllImpl :: (Char -> Boolean) -> Array Int -> Boolean
