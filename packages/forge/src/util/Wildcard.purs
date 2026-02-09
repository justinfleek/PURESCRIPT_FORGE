-- | Wildcard pattern matching
-- | Ported from COMPASS reference: opencode/util/Wildcard.purs
module Forge.Util.Wildcard where

import Prelude
import Data.String as String

-- | Match a string against a wildcard pattern
-- | Supports * (matches any sequence) and ? (matches single character)
match :: String -> String -> Boolean
match pattern str = matchWildcard pattern str

foreign import matchWildcard :: String -> String -> Boolean

-- | Convert wildcard pattern to regex
toRegex :: String -> String
toRegex pattern = convertWildcardToRegex pattern

foreign import convertWildcardToRegex :: String -> String

-- | Check if pattern is a wildcard pattern
isWildcard :: String -> Boolean
isWildcard pattern =
  String.contains (String.Pattern "*") pattern ||
  String.contains (String.Pattern "?") pattern
