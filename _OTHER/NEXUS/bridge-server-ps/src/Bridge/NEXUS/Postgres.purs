-- | Bridge Server NEXUS PostgreSQL Integration
-- | Direct PostgreSQL access for semantic memory operations
module Bridge.NEXUS.Postgres where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff, makeAff, nonCanceler)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Argonaut (Json, jsonParser, decodeJson, encodeJson, class DecodeJson, class EncodeJson, (.:), (.:?))
import Data.Argonaut.Core as AC (stringify)
import Data.Argonaut.Decode (class DecodeJson)
import Data.Array (filter, sortBy, head)
import Data.String (Pattern(..), contains)
import Nexus.Database.Postgres as Postgres
import Nexus.SemanticMemory.VectorClock as VC
import Bridge.NEXUS.CRDT as CRDT

-- | Initialize PostgreSQL pool (called at server startup)
initPostgresPool :: Effect Postgres.PostgresPool
initPostgresPool = Postgres.initPostgresPool

-- | Initialize PostgreSQL pool from URL
initPostgresPoolFromUrl :: String -> Effect Postgres.PostgresPool
initPostgresPoolFromUrl = Postgres.initPostgresPoolFromUrl

-- | Query semantic cells with filters
querySemanticCells :: Postgres.PostgresPool -> Maybe String -> Maybe String -> Maybe String -> Maybe Int -> Aff (Either String Json)
querySemanticCells pool mLevel mDomain mBasin mLimit = do
  result <- Postgres.querySemanticCells pool mLevel mDomain mBasin mLimit
  pure result

-- | Save semantic cell
saveSemanticCell :: Postgres.PostgresPool -> String -> Aff (Either String Unit)
saveSemanticCell pool cellJson = do
  result <- Postgres.saveSemanticCell pool cellJson
  pure result

-- | Load semantic cell by ID
loadSemanticCell :: Postgres.PostgresPool -> String -> Aff (Either String (Maybe Json))
loadSemanticCell pool cellId = do
  result <- Postgres.loadSemanticCell pool cellId
  pure result

-- | Semantic cell record (from PostgreSQL)
type SemanticCellRecord =
  { id :: String
  , name :: String
  , description :: String
  , level :: String
  , domain :: String
  , basin :: String
  , state :: Json  -- JSONB CellState
  , parentId :: Maybe String
  , childrenIds :: Json  -- JSONB array
  , couplingIds :: Json  -- JSONB array
  , createdAt :: String
  , updatedAt :: String
  , vectorClock :: Maybe Json  -- JSONB vector clock
  , regionId :: Maybe String
  , lastSyncedAt :: Maybe String
  }

instance decodeJsonSemanticCellRecord :: DecodeJson SemanticCellRecord where
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
    vectorClock <- obj .:? "vectorClock"
    regionId <- obj .:? "regionId"
    lastSyncedAt <- obj .:? "lastSyncedAt"
    pure { id, name, description, level, domain, basin, state, parentId, childrenIds, couplingIds, createdAt, updatedAt, vectorClock, regionId, lastSyncedAt }

instance encodeJsonSemanticCellRecord :: EncodeJson SemanticCellRecord where
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
    , vectorClock: cell.vectorClock
    , regionId: cell.regionId
    , lastSyncedAt: cell.lastSyncedAt
    }

-- | Create semantic cells from concepts with vector clock (CRDT)
createSemanticCellsWithVC :: Postgres.PostgresPool -> String -> String -> String -> String -> Aff (Either String Json)
createSemanticCellsWithVC pool conceptsJson agentId taskId regionId = do
  -- Parse concepts JSON
  case jsonParser conceptsJson >>= decodeJson of
    Left err -> pure $ Left $ "Failed to parse concepts: " <> err
    Right conceptsObj -> do
      -- Extract concepts array
      let concepts = case conceptsObj `decodeJson` of
            Right obj -> case obj .:? "concepts" of
              Just (Just cs) -> cs
              _ -> []
            Left _ -> []
      
      -- Create cells with vector clock for each concept and save them
      savedCells <- mapM (\concept -> do
        let conceptJson = encodeJson concept
        let cellId = agentId <> "-" <> taskId <> "-" <> (show conceptJson)
        let cellWithVC = CRDT.createCellWithVC regionId cellId "" "" "" "" "" conceptJson
        
        -- Convert cell to JSON and save
        let cellJson = AC.stringify $ encodeJson cellWithVC
        saveResult <- saveSemanticCell pool cellJson
        case saveResult of
          Left err -> pure $ Left err
          Right _ -> pure $ Right cellWithVC
      ) concepts
      
      -- Check for any save errors
      let errors = filter (\r -> case r of Left _ -> true; _ -> false) savedCells
      case head errors of
        Just (Left err) -> pure $ Left $ "Failed to save some cells: " <> err
        _ -> do
          -- Extract successfully saved cells
          let cellsWithVC = map (\r -> case r of Right c -> c; _ -> CRDT.createCellWithVC regionId "" "" "" "" "" "" encodeJson {}) savedCells
          pure $ Right $ encodeJson
            { success: true
            , cellsCreated: length concepts
            , cells: cellsWithVC
            , regionId: regionId
            }

-- | Get agent semantic cells (query by agent ID prefix)
-- | Uses PostgreSQL LIKE query: WHERE id LIKE 'agentId%'
-- | Returns cells with vector clocks for CRDT merge
getAgentSemanticCells :: Postgres.PostgresPool -> String -> Aff (Either String Json)
getAgentSemanticCells pool agentId = do
  -- Query cells with agent ID prefix pattern
  -- Note: This uses a LIKE query via the Haskell layer (querySemanticCellsByPrefix)
  -- For now, query all and filter client-side (would optimize with LIKE query in production)
  result <- Postgres.querySemanticCells pool Nothing Nothing Nothing Nothing
  case result of
    Left err -> pure $ Left err
    Right cellsJson -> do
      -- Parse cells array
      case decodeJson cellsJson of
        Left _ -> pure $ Left "Failed to parse cells JSON"
        Right cellsArray -> do
          -- Filter cells by agent ID prefix
          let prefixPattern = Pattern agentId
          let filteredCells = filter (\c -> 
            case decodeJson c of
              Right cell -> 
                let cellId = fromMaybe "" (cell .:? "id" # fromMaybe (Just ""))
                in contains prefixPattern cellId
              Left _ -> false
          ) cellsArray
          
          -- Find primary cell (highest energy)
          let primaryCell = head $ sortBy (\c1 c2 -> 
            case decodeJson c1, decodeJson c2 of
              Right cell1, Right cell2 -> 
                let energy1 = fromMaybe 0.0 (cell1 .:? "state" >>= \s -> s .:? "energy" # fromMaybe (Just 0.0))
                    energy2 = fromMaybe 0.0 (cell2 .:? "state" >>= \s -> s .:? "energy" # fromMaybe (Just 0.0))
                in compare energy2 energy1  -- Sort descending
              _, _ -> EQ
          ) filteredCells
          
          pure $ Right $ encodeJson
            { success: true
            , agentId: agentId
            , cellsCount: length filteredCells
            , cells: filteredCells
            , primaryCell: primaryCell
            }

-- | Create couplings from relations with vector clock (CRDT)
createCouplingsWithVC :: Postgres.PostgresPool -> String -> String -> String -> Aff (Either String Json)
createCouplingsWithVC pool relationsJson cellMapJson regionId = do
  -- Parse relations JSON
  case jsonParser relationsJson >>= decodeJson of
    Left err -> pure $ Left $ "Failed to parse relations: " <> err
    Right relationsObj -> do
      -- Extract relations array
      let relations = case relationsObj `decodeJson` of
            Right obj -> case obj .:? "relations" of
              Just (Just rs) -> rs
              _ -> []
            Left _ -> []
      
      -- Parse cell map to get cell IDs
      let cellMap = case jsonParser cellMapJson >>= decodeJson of
            Right obj -> case obj .:? "cellMap" of
              Just (Just cm) -> cm
              _ -> encodeJson {}
            Left _ -> encodeJson {}
      
      -- Create couplings by updating cells' coupling_ids and incrementing vector clock
      createdCouplings <- mapM (\relation -> do
        case decodeJson relation of
          Right rel -> do
            -- Extract source and target cell IDs from relation
            let sourceId = fromMaybe "" (rel .:? "source" # fromMaybe (Just ""))
            let targetId = fromMaybe "" (rel .:? "target" # fromMaybe (Just ""))
            
            -- Load both cells
            sourceResult <- loadSemanticCell pool sourceId
            targetResult <- loadSemanticCell pool targetId
            
            case sourceResult, targetResult of
              Right (Just sourceJson), Right (Just targetJson) -> do
                -- Parse cells as SemanticCellWithVC
                case decodeJson sourceJson :: Either _ CRDT.SemanticCellWithVC, decodeJson targetJson :: Either _ CRDT.SemanticCellWithVC of
                  Right sourceCell, Right targetCell -> do
                    -- Increment vector clock for both cells
                    let updatedSource = CRDT.incrementVectorClock regionId sourceCell
                    let updatedTarget = CRDT.incrementVectorClock regionId targetCell
                    
                    -- Add coupling IDs (bidirectional)
                    let sourceCouplings = updatedSource.couplingIds
                    let targetCouplings = updatedTarget.couplingIds
                    let updatedSourceWithCoupling = updatedSource { couplingIds = sourceCouplings <> [targetId] }
                    let updatedTargetWithCoupling = updatedTarget { couplingIds = targetCouplings <> [sourceId] }
                    
                    -- Save updated cells
                    let sourceJsonStr = AC.stringify $ encodeJson updatedSourceWithCoupling
                    let targetJsonStr = AC.stringify $ encodeJson updatedTargetWithCoupling
                    saveSource <- saveSemanticCell pool sourceJsonStr
                    saveTarget <- saveSemanticCell pool targetJsonStr
                    
                    case saveSource, saveTarget of
                      Right _, Right _ -> pure $ Right { sourceId, targetId }
                      Left err, _ -> pure $ Left $ "Failed to save source cell: " <> err
                      _, Left err -> pure $ Left $ "Failed to save target cell: " <> err
                  _, _ -> pure $ Left "Failed to parse cells as SemanticCellWithVC"
              _, _ -> pure $ Left "Failed to load cells"
          Left _ -> pure $ Left "Failed to parse relation"
      ) relations
      
      -- Check for errors
      let errors = filter (\r -> case r of Left _ -> true; _ -> false) createdCouplings
      case head errors of
        Just (Left err) -> pure $ Left err
        _ -> do
          let couplings = map (\r -> case r of Right c -> c; _ -> { sourceId: "", targetId: "" }) createdCouplings
          pure $ Right $ encodeJson
            { success: true
            , couplingsCreated: length relations
            , couplings: couplings
            , regionId: regionId
            }

-- | Merge semantic cells using CRDT logic (for replication)
mergeSemanticCells :: Postgres.PostgresPool -> String -> Json -> Json -> Aff (Either String Json)
mergeSemanticCells pool regionId cell1Json cell2Json = do
  -- Parse both cells
  case decodeJson cell1Json, decodeJson cell2Json of
    Right c1, Right c2 -> do
      -- Merge using CRDT logic
      let mergedCell = CRDT.mergeCells regionId c1 c2
      
      -- Save merged cell to PostgreSQL
      let mergedCellJson = AC.stringify $ encodeJson mergedCell
      saveResult <- saveSemanticCell pool mergedCellJson
      case saveResult of
        Left err -> pure $ Left $ "Failed to save merged cell: " <> err
        Right _ -> pure $ Right $ encodeJson mergedCell
    _, _ -> pure $ Left "Failed to parse cells for merge"
