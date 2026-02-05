-- | Wildcard pattern matching
module Opencode.Util.Wildcard where

import Prelude
import Data.String as String
import Data.Array as Array

-- | Match a string against a wildcard pattern
-- | Supports * (matches any sequence) and ? (matches single character)
match :: String -> String -> Boolean
match pattern str = matchWildcard pattern str
  where
    foreign import matchWildcard :: String -> String -> Boolean

-- | Convert wildcard pattern to regex
toRegex :: String -> String
toRegex pattern = convertWildcardToRegex pattern
  where
    foreign import convertWildcardToRegex :: String -> String

-- | Check if pattern is a wildcard pattern
isWildcard :: String -> Boolean
isWildcard pattern = 
  String.contains (String.Pattern "*") pattern || 
  String.contains (String.Pattern "?") pattern
