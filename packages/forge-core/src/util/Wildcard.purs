-- | Wildcard pattern matching
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/util/wildcard.ts
module Forge.Util.Wildcard where

import Prelude

-- | Match a string against a wildcard pattern
-- | Supports * and ? wildcards
match :: String -> String -> Boolean
match pattern str = false -- TODO: Implement

-- | Convert wildcard pattern to regex
toRegex :: String -> String
toRegex pattern = pattern -- TODO: Implement

-- | Check if pattern is a wildcard pattern
isWildcard :: String -> Boolean
isWildcard pattern = false -- TODO: Check for * or ?
