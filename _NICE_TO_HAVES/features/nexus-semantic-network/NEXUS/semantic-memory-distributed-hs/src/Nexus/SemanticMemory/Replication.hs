-- | Nexus Semantic Memory - PostgreSQL Logical Replication
-- | Listens to PostgreSQL logical replication stream for semantic cell changes
-- | Applies CRDT merge logic when cells are replicated across regions
{-# LANGUAGE OverloadedStrings #-}
module Nexus.SemanticMemory.Replication where

import Nexus.SemanticMemory.CRDT (mergeCells, SemanticCell(..), CellState(..), compareVectorClocks, mergeVectorClocks, VectorClock)
import Nexus.Database.Postgres (PostgresPool, withConnection)
import Nexus.Database.Postgres.Operations (SemanticCellRecord(..), loadSemanticCell, saveSemanticCell, querySemanticCellsByPrefix)
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.FromRow
import qualified Data.Text as T
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Types as AesonTypes
import Data.Time.Clock (UTCTime, getCurrentTime)
import Control.Concurrent (forkIO, threadDelay)
import Control.Exception (catch, SomeException)
import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.HashMap.Strict as HM
import qualified Data.Vector as V
import qualified Data.List as L

-- | Replication event from PostgreSQL logical replication
data ReplicationEvent = ReplicationEvent
  { eventType :: T.Text  -- "INSERT", "UPDATE", "DELETE"
  , cellId :: T.Text
  , cellData :: Aeson.Value  -- Full cell JSONB data
  , sourceRegion :: T.Text  -- Region where change originated
  , timestamp :: UTCTime
  } deriving (Show)

-- | Replication listener configuration
data ReplicationConfig = ReplicationConfig
  { configPool :: PostgresPool
  , configRegionId :: T.Text  -- Current region ID
  , configSlotName :: T.Text  -- Logical replication slot name
  , configPublicationName :: T.Text  -- Publication name
  , onCellReplicated :: SemanticCell -> IO ()  -- Callback for replicated cells
  }

-- | Start logical replication listener
-- | Creates replication slot and starts streaming changes
startReplicationListener :: ReplicationConfig -> IO ()
startReplicationListener config = do
  -- Create logical replication slot if it doesn't exist
  createReplicationSlot config
  
  -- Start replication stream in background thread
  forkIO $ replicationLoop config
  return ()

-- | Create logical replication slot
createReplicationSlot :: ReplicationConfig -> IO ()
createReplicationSlot config = withConnection (configPool config) $ \conn -> do
  let slotName = configSlotName config
  -- Check if slot exists
  slots <- query conn "SELECT slot_name FROM pg_replication_slots WHERE slot_name = ?" (Only slotName)
  case slots of
    [] -> do
      -- Create replication slot
      execute_ conn $ Query $ "SELECT pg_create_logical_replication_slot('" <> slotName <> "', 'pgoutput')"
      return ()
    _ -> return ()  -- Slot already exists

-- | Main replication loop
-- | Reads changes from logical replication stream and applies CRDT merge
replicationLoop :: ReplicationConfig -> IO ()
replicationLoop config = do
  withConnection (configPool config) $ \conn -> do
    -- Start replication stream
    -- In production, would use pgoutput plugin and parse WAL messages
    -- For now, poll semantic_cells table for changes with vector_clock updates
    pollForChanges config conn

-- | Poll for changes (simplified - in production would use logical replication stream)
pollForChanges :: ReplicationConfig -> Connection -> IO ()
pollForChanges config conn = do
  -- Query for cells that need replication (have vector_clock entries from other regions)
  -- In production, this would be replaced with actual logical replication stream parsing
  let currentRegionId = configRegionId config
  let queryStr = "SELECT id, name, description, level, domain, basin, state, parent_id, children_ids, coupling_ids, created_at, updated_at, vector_clock, region_id, last_synced_at FROM semantic_cells WHERE (region_id IS NULL OR region_id != $1) AND updated_at > COALESCE((SELECT MAX(last_synced_at) FROM semantic_cells WHERE region_id = $1), '1970-01-01'::timestamp) ORDER BY updated_at DESC LIMIT 100"
  
  -- Execute query
  cells <- query conn (Query queryStr) (Only currentRegionId) :: IO [SemanticCellRecord]
  
  -- Process each cell: load existing, merge, save
  mapM_ (\cellRecord -> do
    -- Convert record to SemanticCell
    incomingCell <- recordToSemanticCell cellRecord
    case incomingCell of
      Just incoming -> do
        -- Load existing cell from local database
        existingCell <- loadCellFromDatabase (configPool config) (cellId incoming)
        case existingCell of
          Nothing -> do
            -- Cell doesn't exist locally, save incoming cell
            saveCellToDatabase (configPool config) incoming
            (onCellReplicated config) incoming
          Just existing -> do
            -- Merge cells using CRDT logic
            let mergedCell = mergeCells existing incoming
            saveCellToDatabase (configPool config) mergedCell
            (onCellReplicated config) mergedCell
      Nothing -> return ()  -- Skip invalid cells
    ) cells
  
  -- Update last_synced_at timestamp for current region
  updateLastSyncedAt conn currentRegionId
  
  -- Poll every 1 second
  threadDelay 1000000  -- 1 second in microseconds
  
  -- Continue polling
  pollForChanges config conn

-- | Update last_synced_at timestamp for region
updateLastSyncedAt :: Connection -> T.Text -> IO ()
updateLastSyncedAt conn regionId = do
  currentTime <- getCurrentTime
  execute conn "UPDATE semantic_cells SET last_synced_at = $1 WHERE region_id = $2" (currentTime, regionId)
  return ()

-- | Apply CRDT merge for a replicated cell
-- | Loads existing cell, merges with incoming cell, saves result
-- | This is the core CRDT merge handler for replication events
applyCRDTMerge :: PostgresPool -> T.Text -> SemanticCell -> IO (Maybe SemanticCell)
applyCRDTMerge pool incomingCellId incomingCell = do
  -- Load existing cell from local database
  existingCell <- loadCellFromDatabase pool incomingCellId
  
  case existingCell of
    Nothing -> do
      -- Cell doesn't exist locally, save incoming cell
      saveCellToDatabase pool incomingCell
      return $ Just incomingCell
    Just existing -> do
      -- Merge cells using CRDT logic (commutative, associative, idempotent)
      let mergedCell = mergeCells existing incomingCell
      saveCellToDatabase pool mergedCell
      return $ Just mergedCell

-- | Load cell from database
loadCellFromDatabase :: PostgresPool -> T.Text -> IO (Maybe SemanticCell)
loadCellFromDatabase pool cellId = do
  mRecord <- loadSemanticCell pool cellId
  case mRecord of
    Nothing -> return Nothing
    Just record -> recordToSemanticCell record

-- | Save cell to database
saveCellToDatabase :: PostgresPool -> SemanticCell -> IO ()
saveCellToDatabase pool cell = do
  record <- semanticCellToRecord cell
  saveSemanticCell pool record

-- | Convert SemanticCellRecord to SemanticCell
recordToSemanticCell :: SemanticCellRecord -> IO (Maybe SemanticCell)
recordToSemanticCell record = do
  -- Parse cell state from JSONB
  cellState <- case Aeson.fromJSON (cellState record) of
    Aeson.Success obj -> do
    Just (Aeson.Object obj) -> do
      -- Parse position array (512 dimensions)
      position <- case Aeson.lookup "position" obj of
        Just (Aeson.Array arr) -> return $ V.fromList $ map (\v -> case v of Aeson.Number n -> realToFrac n; _ -> 0.0) $ V.toList arr
        _ -> return $ V.replicate 512 0.0
      -- Parse velocity array
      velocity <- case Aeson.lookup "velocity" obj of
        Just (Aeson.Array arr) -> return $ V.fromList $ map (\v -> case v of Aeson.Number n -> realToFrac n; _ -> 0.0) $ V.toList arr
        _ -> return $ V.replicate 512 0.0
      -- Parse scalar fields
      let spin = case Aeson.lookup "spin" obj of
            Just (Aeson.Number n) -> realToFrac n
            _ -> 0.0
      let grade = case Aeson.lookup "grade" obj of
            Just (Aeson.Number n) -> realToFrac n
            _ -> 0.0
      let energy = case Aeson.lookup "energy" obj of
            Just (Aeson.Number n) -> realToFrac n
            _ -> 0.0
      return $ Just $ CellState position velocity spin grade energy
    Aeson.Error _ -> return Nothing
  
  case cellState of
    Nothing -> return Nothing
    Just state -> do
      -- Parse children_ids and coupling_ids from JSONB arrays
      childrenIds <- case Aeson.fromJSON (cellChildrenIds record) of
        Aeson.Success (Aeson.Array arr) -> return $ map (\v -> case v of Aeson.String s -> T.unpack s; _ -> "") $ V.toList arr
        _ -> return []
      couplingIds <- case Aeson.fromJSON (cellCouplingIds record) of
        Aeson.Success (Aeson.Array arr) -> return $ map (\v -> case v of Aeson.String s -> T.unpack s; _ -> "") $ V.toList arr
        _ -> return []
      
      -- Parse vector clock from JSONB
      vectorClock <- case cellVectorClock record of
        Just vcJson -> case Aeson.fromJSON vcJson of
          Aeson.Success (Aeson.Object obj) -> do
            let vcMap = HM.fromList $ map (\(k, v) -> (T.pack k, case v of Aeson.Number n -> floor n; _ -> 0)) $ Aeson.toKeyValue obj
            return vcMap
          _ -> return HM.empty
        Nothing -> return HM.empty
      
      return $ Just $ SemanticCell
        { cellId = cellId record
        , cellName = cellName record
        , cellDescription = cellDescription record
        , cellLevel = cellLevel record
        , cellDomain = cellDomain record
        , cellBasin = cellBasin record
        , cellState = state
        , cellParentId = cellParentId record
        , cellChildrenIds = map T.pack childrenIds
        , cellCouplingIds = map T.pack couplingIds
        , cellCreatedAt = cellCreatedAt record
        , cellUpdatedAt = cellUpdatedAt record
        , cellVectorClock = vectorClock
        , cellRegionId = cellRegionId record
        }

-- | Convert SemanticCell to SemanticCellRecord
semanticCellToRecord :: SemanticCell -> IO SemanticCellRecord
semanticCellToRecord cell = do
  currentTime <- getCurrentTime
  
  -- Convert cell state to JSONB
  let stateJson = Aeson.object
        [ "position" .= Aeson.Array (V.map Aeson.Number $ V.map realToFrac $ position $ cellState cell)
        , "velocity" .= Aeson.Array (V.map Aeson.Number $ V.map realToFrac $ velocity $ cellState cell)
        , "spin" .= Aeson.Number (realToFrac $ spin $ cellState cell)
        , "grade" .= Aeson.Number (realToFrac $ grade $ cellState cell)
        , "energy" .= Aeson.Number (realToFrac $ energy $ cellState cell)
        ]
  
  -- Convert children_ids and coupling_ids to JSONB arrays
  let childrenIdsJson = Aeson.Array $ V.fromList $ map Aeson.String $ cellChildrenIds cell
  let couplingIdsJson = Aeson.Array $ V.fromList $ map Aeson.String $ cellCouplingIds cell
  
  -- Convert vector clock to JSONB
  let vectorClockJson = Just $ Aeson.object $ map (\(k, v) -> (T.unpack k, Aeson.Number $ fromIntegral v)) $ HM.toList $ cellVectorClock cell
  
  return $ SemanticCellRecord
    { cellId = cellId cell
    , cellName = cellName cell
    , cellDescription = cellDescription cell
    , cellLevel = cellLevel cell
    , cellDomain = cellDomain cell
    , cellBasin = cellBasin cell
    , cellState = stateJson
    , cellParentId = cellParentId cell
    , cellChildrenIds = childrenIdsJson
    , cellCouplingIds = couplingIdsJson
    , cellCreatedAt = cellCreatedAt cell
    , cellUpdatedAt = cellUpdatedAt cell
    , cellVectorClock = vectorClockJson
    , cellRegionId = cellRegionId cell
    , cellLastSyncedAt = Just currentTime
    }

-- | Stop replication listener
stopReplicationListener :: ReplicationConfig -> IO ()
stopReplicationListener config = do
  -- Drop replication slot
  withConnection (configPool config) $ \conn -> do
    let slotName = configSlotName config
    execute_ conn $ Query $ "SELECT pg_drop_replication_slot('" <> slotName <> "')"
  return ()
