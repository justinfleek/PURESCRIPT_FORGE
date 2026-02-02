-- | Array utilities
-- | Migrated from opencode-dev/packages/util/src/array.ts
module Opencode.Util.Array
  ( findLast
  ) where

import Prelude
import Data.Array (length, (!!))
import Data.Maybe (Maybe(..))

-- | Find the last element matching a predicate
findLast :: forall a. (a -> Int -> Boolean) -> Array a -> Maybe a
findLast predicate items = go (length items - 1)
  where
  go :: Int -> Maybe a
  go i
    | i < 0 = Nothing
    | otherwise = case items !! i of
        Nothing -> Nothing
        Just item ->
          if predicate item i
            then Just item
            else go (i - 1)
