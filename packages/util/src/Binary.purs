-- | Binary search utilities
-- | Migrated from opencode-dev/packages/util/src/binary.ts
module Opencode.Util.Binary
  ( SearchResult
  , search
  , insert
  ) where

import Prelude
import Data.Array (length, (!!), insertAt)
import Data.Maybe (Maybe(..), fromMaybe)

type SearchResult = { found :: Boolean, index :: Int }

-- | Binary search for an element by ID
search :: forall a. Array a -> String -> (a -> String) -> SearchResult
search array id compare = go 0 (length array - 1)
  where
  go :: Int -> Int -> SearchResult
  go left right
    | left > right = { found: false, index: left }
    | otherwise =
        let mid = (left + right) / 2
        in case array !! mid of
          Nothing -> { found: false, index: left }
          Just item ->
            let midId = compare item
            in if midId == id
              then { found: true, index: mid }
              else if midId < id
                then go (mid + 1) right
                else go left (mid - 1)

-- | Insert an item maintaining sorted order
insert :: forall a. Array a -> a -> (a -> String) -> Array a
insert array item compare =
  let id = compare item
      idx = findInsertIndex array id compare 0 (length array)
  in fromMaybe array (insertAt idx item array)

findInsertIndex :: forall a. Array a -> String -> (a -> String) -> Int -> Int -> Int
findInsertIndex array id compare left right
  | left >= right = left
  | otherwise =
      let mid = (left + right) / 2
      in case array !! mid of
        Nothing -> left
        Just item ->
          if compare item < id
            then findInsertIndex array id compare (mid + 1) right
            else findInsertIndex array id compare left mid
