-- | Nexus Semantic Memory - CRDT Merge Logic
-- | Conflict-free Replicated Data Type (CRDT) merge operations for semantic cells
-- | Ensures eventual consistency across distributed regions
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module Nexus.SemanticMemory.CRDT where

import qualified Data.Aeson as Aeson
import qualified Data.Text as T
import Data.Time.Clock (UTCTime)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Ord (max, min)
import qualified Data.HashMap.Strict as HM
import qualified Data.Vector as V
import qualified Data.Set as Set
import Data.List (nub)

-- | Vector clock entry (region -> timestamp)
type VectorClock = HM.HashMap T.Text Int

-- | Semantic cell state (from JSONB)
data CellState = CellState
  { position :: V.Vector Double  -- 512-dimensional embedding position
  , velocity :: V.Vector Double  -- Velocity vector
  , spin :: Double  -- Angular momentum
  , grade :: Double  -- Energy level (0.0 to 1.0)
  , energy :: Double  -- Current energy
  } deriving (Show, Eq)

-- | Semantic cell with vector clock
data SemanticCell = SemanticCell
  { cellId :: T.Text
  , cellName :: T.Text
  , cellDescription :: T.Text
  , cellLevel :: T.Text
  , cellDomain :: T.Text
  , cellBasin :: T.Text
  , cellState :: CellState
  , cellParentId :: Maybe T.Text
  , cellChildrenIds :: [T.Text]
  , cellCouplingIds :: [T.Text]
  , cellCreatedAt :: UTCTime
  , cellUpdatedAt :: UTCTime
  , cellVectorClock :: VectorClock  -- Vector clock for causal ordering
  , cellRegionId :: Maybe T.Text  -- Region where cell was created/updated
  } deriving (Show, Eq)

-- | Compare vector clocks (returns: LT, EQ, GT, or CONCURRENT)
data VectorClockOrder = LT | EQ | GT | CONCURRENT deriving (Show, Eq)

-- | Compare two vector clocks
-- | Returns LT if vc1 < vc2 (vc1 happened before vc2)
-- | Returns GT if vc1 > vc2 (vc1 happened after vc2)
-- | Returns EQ if vc1 == vc2
-- | Returns CONCURRENT if vc1 || vc2 (concurrent events)
compareVectorClocks :: VectorClock -> VectorClock -> VectorClockOrder
compareVectorClocks vc1 vc2 =
  let allRegions = Set.fromList (HM.keys vc1 ++ HM.keys vc2)
      vc1Less = Set.foldr (\r acc -> acc && (HM.lookupDefault 0 r vc1 <= HM.lookupDefault 0 r vc2)) True allRegions
      vc2Less = Set.foldr (\r acc -> acc && (HM.lookupDefault 0 r vc2 <= HM.lookupDefault 0 r vc1)) True allRegions
      vc1StrictLess = Set.foldr (\r acc -> acc || (HM.lookupDefault 0 r vc1 < HM.lookupDefault 0 r vc2)) False allRegions
      vc2StrictLess = Set.foldr (\r acc -> acc || (HM.lookupDefault 0 r vc2 < HM.lookupDefault 0 r vc1)) False allRegions
  in if vc1Less && vc2Less then EQ
     else if vc1Less && vc2StrictLess then LT
     else if vc2Less && vc1StrictLess then GT
     else CONCURRENT

-- | Merge two vector clocks (take maximum for each region)
mergeVectorClocks :: VectorClock -> VectorClock -> VectorClock
mergeVectorClocks vc1 vc2 =
  let allRegions = HM.keysSet vc1 `HM.union` HM.keysSet vc2
  in HM.fromList $ map (\r -> (r, max (HM.lookupDefault 0 r vc1) (HM.lookupDefault 0 r vc2))) allRegions

-- | Increment vector clock for a region
incrementVectorClock :: VectorClock -> T.Text -> VectorClock
incrementVectorClock vc region =
  HM.insert region (HM.lookupDefault 0 region vc + 1) vc

-- | Merge two semantic cells using CRDT merge logic
-- | Properties:
-- |   - Commutative: mergeCells c1 c2 == mergeCells c2 c1
-- |   - Associative: mergeCells (mergeCells c1 c2) c3 == mergeCells c1 (mergeCells c2 c3)
-- |   - Idempotent: mergeCells c c == c
mergeCells :: SemanticCell -> SemanticCell -> SemanticCell
mergeCells c1 c2
  | cellId c1 /= cellId c2 = error "Cannot merge cells with different IDs"
  | otherwise =
    let -- Merge vector clocks (take maximum for each region)
        mergedVC = mergeVectorClocks (cellVectorClock c1) (cellVectorClock c2)
        
        -- Determine which cell is "newer" based on vector clock
        vcOrder = compareVectorClocks (cellVectorClock c1) (cellVectorClock c2)
        
        -- Choose cell with later updated_at timestamp (tie-breaker)
        (chosenCell, otherCell) = if cellUpdatedAt c1 >= cellUpdatedAt c2
                                   then (c1, c2)
                                   else (c2, c1)
        
        -- Merge state: take weighted average of position, velocity based on energy
        -- Higher energy cell has more influence
        mergedState = mergeCellStates (cellState chosenCell) (cellState otherCell)
        
        -- Merge lists: union of children_ids and coupling_ids
        mergedChildrenIds = nub $ cellChildrenIds c1 ++ cellChildrenIds c2
        mergedCouplingIds = nub $ cellCouplingIds c1 ++ cellCouplingIds c2
        
        -- Take most recent parent_id (if both exist, prefer from newer cell)
        mergedParentId = case (cellParentId chosenCell, cellParentId otherCell) of
          (Just p1, Just p2) -> if cellUpdatedAt c1 >= cellUpdatedAt c2 then Just p1 else Just p2
          (Just p, Nothing) -> Just p
          (Nothing, Just p) -> Just p
          (Nothing, Nothing) -> Nothing
        
        -- Use latest updated_at timestamp
        mergedUpdatedAt = max (cellUpdatedAt c1) (cellUpdatedAt c2)
        
    in SemanticCell
        { cellId = cellId c1
        , cellName = cellName chosenCell  -- Prefer newer name
        , cellDescription = cellDescription chosenCell  -- Prefer newer description
        , cellLevel = cellLevel chosenCell
        , cellDomain = cellDomain chosenCell
        , cellBasin = cellBasin chosenCell
        , cellState = mergedState
        , cellParentId = mergedParentId
        , cellChildrenIds = mergedChildrenIds
        , cellCouplingIds = mergedCouplingIds
        , cellCreatedAt = min (cellCreatedAt c1) (cellCreatedAt c2)  -- Earliest creation time
        , cellUpdatedAt = mergedUpdatedAt
        , cellVectorClock = mergedVC
        , cellRegionId = cellRegionId chosenCell  -- Prefer newer region
        }

-- | Merge two cell states (weighted average based on energy)
mergeCellStates :: CellState -> CellState -> CellState
mergeCellStates s1 s2 =
  let totalEnergy = energy s1 + energy s2
      weight1 = if totalEnergy > 0 then energy s1 / totalEnergy else 0.5
      weight2 = if totalEnergy > 0 then energy s2 / totalEnergy else 0.5
      
      -- Weighted average of position
      mergedPosition = V.zipWith (\p1 p2 -> weight1 * p1 + weight2 * p2) (position s1) (position s2)
      
      -- Weighted average of velocity
      mergedVelocity = V.zipWith (\v1 v2 -> weight1 * v1 + weight2 * v2) (velocity s1) (velocity s2)
      
      -- Weighted average of spin
      mergedSpin = weight1 * spin s1 + weight2 * spin s2
      
      -- Maximum grade (higher grade = more refined)
      mergedGrade = max (grade s1) (grade s2)
      
      -- Sum of energies
      mergedEnergy = energy s1 + energy s2
      
  in CellState
      { position = mergedPosition
      , velocity = mergedVelocity
      , spin = mergedSpin
      , grade = mergedGrade
      , energy = mergedEnergy
      }

