-- | Bridge Server NEXUS - CRDT Integration
-- | CRDT merge operations for distributed semantic memory
module Bridge.NEXUS.CRDT where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff, makeAff, nonCanceler)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Argonaut (Json, encodeJson, decodeJson, class DecodeJson, class EncodeJson, (.:), (.:?))
import Data.Argonaut.Core as AC (stringify)
import Nexus.SemanticMemory.VectorClock as VC
import Nexus.Database.Postgres as Postgres

-- | Semantic cell with vector clock (for CRDT operations)
type SemanticCellWithVC =
  { id :: String
  , name :: String
  , description :: String
  , level :: String
  , domain :: String
  , basin :: String
  , state :: Json  -- JSONB CellState
  , parentId :: Maybe String
  , childrenIds :: Array String
  , couplingIds :: Array String
  , createdAt :: String
  , updatedAt :: String
  , vectorClock :: VC.VectorClock  -- Vector clock for causal ordering
  , regionId :: Maybe String  -- Region where cell was created/updated
  }

instance decodeJsonSemanticCellWithVC :: DecodeJson SemanticCellWithVC where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    name <- obj .: "name"
    description <- obj .: "description"
    level <- obj .: "level"
    domain <- obj .: "domain"
    basin <- obj .: "basin"
    state <- obj .: "state"
    parentId <- obj .:? "parentId"
    childrenIds <- obj .: "childrenIds"
    couplingIds <- obj .: "couplingIds"
    createdAt <- obj .: "createdAt"
    updatedAt <- obj .: "updatedAt"
    vectorClockJson <- obj .:? "vectorClock"
    vectorClock <- case vectorClockJson of
      Just vcJson -> case decodeJson vcJson of
        Right vc -> pure vc
        Left _ -> pure VC.empty
      Nothing -> pure VC.empty
    regionId <- obj .:? "regionId"
    pure { id, name, description, level, domain, basin, state, parentId, childrenIds, couplingIds, createdAt, updatedAt, vectorClock, regionId }

instance encodeJsonSemanticCellWithVC :: EncodeJson SemanticCellWithVC where
  encodeJson cell = encodeJson
    { id: cell.id
    , name: cell.name
    , description: cell.description
    , level: cell.level
    , domain: cell.domain
    , basin: cell.basin
    , state: cell.state
    , parentId: cell.parentId
    , childrenIds: cell.childrenIds
    , couplingIds: cell.couplingIds
    , createdAt: cell.createdAt
    , updatedAt: cell.updatedAt
    , vectorClock: encodeJson cell.vectorClock
    , regionId: cell.regionId
    }

-- | Merge two semantic cells using CRDT logic
-- | Properties: commutative, associative, idempotent
mergeCells :: String -> SemanticCellWithVC -> SemanticCellWithVC -> SemanticCellWithVC
mergeCells regionId c1 c2
  | c1.id /= c2.id = c1  -- Error case (should not happen)
  | otherwise =
    let
      -- Merge vector clocks (take maximum for each region)
      mergedVC = VC.merge c1.vectorClock c2.vectorClock
      
      -- Determine which cell is "newer" based on vector clock
      vcOrder = VC.compare c1.vectorClock c2.vectorClock
      
      -- Choose cell with later updated_at timestamp (tie-breaker)
      chosenCell = if c1.updatedAt >= c2.updatedAt then c1 else c2
      
      -- Merge lists: union of children_ids and coupling_ids
      mergedChildrenIds = nub $ c1.childrenIds <> c2.childrenIds
      mergedCouplingIds = nub $ c1.couplingIds <> c2.couplingIds
      
      -- Take most recent parent_id
      mergedParentId = case chosenCell.parentId of
        Just p -> Just p
        Nothing -> c1.parentId <|> c2.parentId
      
      -- Use latest updated_at timestamp
      mergedUpdatedAt = if c1.updatedAt >= c2.updatedAt then c1.updatedAt else c2.updatedAt
      
    in
      { id: c1.id
      , name: chosenCell.name
      , description: chosenCell.description
      , level: chosenCell.level
      , domain: chosenCell.domain
      , basin: chosenCell.basin
      , state: chosenCell.state  -- In production, would merge states based on energy
      , parentId: mergedParentId
      , childrenIds: mergedChildrenIds
      , couplingIds: mergedCouplingIds
      , createdAt: if c1.createdAt <= c2.createdAt then c1.createdAt else c2.createdAt
      , updatedAt: mergedUpdatedAt
      , vectorClock: mergedVC
      , regionId: Just regionId  -- Current region
      }

-- | Increment vector clock for a region (when creating/updating cell)
incrementVectorClock :: String -> SemanticCellWithVC -> SemanticCellWithVC
incrementVectorClock regionId cell =
  cell { vectorClock = VC.increment regionId cell.vectorClock }

-- | Create new semantic cell with initial vector clock
createCellWithVC :: String -> String -> String -> String -> String -> String -> Json -> SemanticCellWithVC
createCellWithVC regionId cellId name description level domain basin state =
  { id: cellId
  , name: name
  , description: description
  , level: level
  , domain: domain
  , basin: basin
  , state: state
  , parentId: Nothing
  , childrenIds: []
  , couplingIds: []
  , createdAt: ""  -- Would use current timestamp
  , updatedAt: ""  -- Would use current timestamp
  , vectorClock: VC.increment regionId VC.empty
  , regionId: Just regionId
  }

import Data.Array (nub)
import Data.Maybe ((<|>))

-- | Foreign import for region ID
foreign import getRegionId :: Effect String
