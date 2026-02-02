-- | Nexus Semantic Memory - Vector Clock
-- | Vector clock data structure and tracking for causal ordering
-- | Used for CRDT merge operations in distributed semantic memory
module Nexus.SemanticMemory.VectorClock where

import Prelude

import Data.Argonaut (Json, encodeJson, decodeJson, class EncodeJson, class DecodeJson, (.:), (.:?))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

-- | Vector clock: maps region IDs to logical timestamps
type VectorClock = Map.Map String Int

-- | Vector clock comparison result
data VectorClockOrder = LT | EQ | GT | CONCURRENT

derive instance eqVectorClockOrder :: Eq VectorClockOrder
derive instance ordVectorClockOrder :: Ord VectorClockOrder

instance showVectorClockOrder :: Show VectorClockOrder where
  show LT = "LT"
  show EQ = "EQ"
  show GT = "GT"
  show CONCURRENT = "CONCURRENT"

-- | Empty vector clock
empty :: VectorClock
empty = Map.empty

-- | Create vector clock from list of region/timestamp pairs
fromList :: Array (Tuple String Int) -> VectorClock
fromList = Map.fromFoldable

-- | Convert vector clock to list
toList :: VectorClock -> Array (Tuple String Int)
toList = Map.toUnfoldable

-- | Get timestamp for a region (defaults to 0)
get :: String -> VectorClock -> Int
get region vc = Map.lookup region vc # fromMaybe 0

-- | Set timestamp for a region
set :: String -> Int -> VectorClock -> VectorClock
set = Map.insert

-- | Increment vector clock for a region
increment :: String -> VectorClock -> VectorClock
increment region vc = Map.insert region (get region vc + 1) vc

-- | Merge two vector clocks (take maximum for each region)
-- | Property: merge vc1 vc2 == merge vc2 vc1 (commutative)
merge :: VectorClock -> VectorClock -> VectorClock
merge vc1 vc2 =
  let allRegions = Map.keys vc1 <> Map.keys vc2
      mergedEntries = map (\region ->
        Tuple region (max (get region vc1) (get region vc2))
      ) allRegions
  in fromList mergedEntries

-- | Compare two vector clocks
-- | Returns LT if vc1 < vc2 (vc1 happened before vc2)
-- | Returns GT if vc1 > vc2 (vc1 happened after vc2)
-- | Returns EQ if vc1 == vc2
-- | Returns CONCURRENT if vc1 || vc2 (concurrent events)
compare :: VectorClock -> VectorClock -> VectorClockOrder
compare vc1 vc2 =
  let allRegions = Map.keys vc1 <> Map.keys vc2
      vc1Less = all (\r -> get r vc1 <= get r vc2) allRegions
      vc2Less = all (\r -> get r vc2 <= get r vc1) allRegions
      vc1StrictLess = any (\r -> get r vc1 < get r vc2) allRegions
      vc2StrictLess = any (\r -> get r vc2 < get r vc1) allRegions
  in if vc1Less && vc2Less then EQ
     else if vc1Less && vc2StrictLess then LT
     else if vc2Less && vc1StrictLess then GT
     else CONCURRENT

-- | Check if vc1 happened before vc2
happenedBefore :: VectorClock -> VectorClock -> Boolean
happenedBefore vc1 vc2 = compare vc1 vc2 == LT

-- | Check if vc1 happened after vc2
happenedAfter :: VectorClock -> VectorClock -> Boolean
happenedAfter vc1 vc2 = compare vc1 vc2 == GT

-- | Check if two vector clocks are concurrent
isConcurrent :: VectorClock -> VectorClock -> Boolean
isConcurrent vc1 vc2 = compare vc1 vc2 == CONCURRENT

-- | JSON encoding/decoding for vector clock
instance encodeJsonVectorClock :: EncodeJson VectorClock where
  encodeJson vc = encodeJson $ Map.toUnfoldable vc

instance decodeJsonVectorClock :: DecodeJson VectorClock where
  decodeJson json = do
    entries <- decodeJson json
    pure $ Map.fromFoldable entries
