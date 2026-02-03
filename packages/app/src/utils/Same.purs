-- | Array equality utility
-- | Migrated from: forge-dev/packages/app/src/utils/same.ts (7 lines)
module Sidepanel.Utils.Same
  ( same
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))

-- | Check if two arrays are referentially equal or have identical elements
-- | Uses reference equality first, then element-wise comparison
-- | Useful for memoization and shouldUpdate checks
same :: forall a. Eq a => Maybe (Array a) -> Maybe (Array a) -> Boolean
same maybeA maybeB = case maybeA, maybeB of
  -- Reference equality (same array)
  Just a, Just b | unsafeRefEq a b -> true
  
  -- One or both are Nothing
  Nothing, Nothing -> true
  Nothing, _ -> false
  _, Nothing -> false
  
  -- Both present, compare lengths and elements
  Just a, Just b ->
    Array.length a == Array.length b &&
    Array.zip a b # Array.all (\(x /\ y) -> x == y)

-- | Non-Maybe version for direct array comparison
sameArray :: forall a. Eq a => Array a -> Array a -> Boolean
sameArray a b
  | unsafeRefEq a b = true
  | Array.length a /= Array.length b = false
  | otherwise = Array.zip a b # Array.all (\(x /\ y) -> x == y)

-- | Foreign import for reference equality check
foreign import unsafeRefEq :: forall a. a -> a -> Boolean

-- | Tuple operator for zip
infixr 6 Tuple as /\

data Tuple a b = Tuple a b
