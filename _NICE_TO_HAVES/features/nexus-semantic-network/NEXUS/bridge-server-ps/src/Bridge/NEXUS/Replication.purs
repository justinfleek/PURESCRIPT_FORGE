-- | Bridge Server NEXUS - Replication API
-- | API endpoints for CRDT merge operations and replication
module Bridge.NEXUS.Replication where

import Prelude

import Bridge.Protocol.JsonRpc (JsonRpcRequest, JsonRpcResponse, JsonRpcError)
import Bridge.NEXUS.CRDT as CRDT
import Bridge.NEXUS.Postgres as Postgres
import Effect (Effect)
import Effect.Aff (launchAff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Argonaut (encodeJson, decodeJson, Json, jsonParser)
import Data.Argonaut.Core as AC (stringify)
import Data.Argonaut.Decode (class DecodeJson, (.:), (.:?))
import Nexus.Database.Postgres as NexusPostgres

-- | Foreign imports
foreign import getPostgresPool :: Effect NexusPostgres.PostgresPool
foreign import getRegionId :: Effect String

-- | Merge cells request
type MergeCellsRequest =
  { cell1 :: Json
  , cell2 :: Json
  }

instance decodeJsonMergeCellsRequest :: DecodeJson MergeCellsRequest where
  decodeJson json = do
    obj <- decodeJson json
    cell1 <- obj .: "cell1"
    cell2 <- obj .: "cell2"
    pure { cell1, cell2 }

-- | Merge semantic cells using CRDT logic
-- | Endpoint: nexus.cells.merge
nexusCellsMerge :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusCellsMerge req = do
  regionId <- getRegionId
  postgresPool <- getPostgresPool
  
  -- Parse params
  let parsedParams = case req.params of
        Just paramsStr -> case jsonParser paramsStr >>= decodeJson of
          Right p -> Just p
          Left _ -> Nothing
        Nothing -> Nothing
  
  case parsedParams of
    Just params -> do
      -- Parse both cells
      case decodeJson params.cell1, decodeJson params.cell2 of
        Right c1, Right c2 -> do
          -- Merge using CRDT logic
          let mergedCell = CRDT.mergeCells regionId c1 c2
          
          -- Save merged cell to PostgreSQL
          saveResult <- launchAff $ Postgres.saveSemanticCell postgresPool (AC.stringify $ encodeJson mergedCell)
          
          case saveResult of
            Left err -> pure $ Right
              { jsonrpc: "2.0"
              , id: req.id
              , result: Nothing
              , error: Just { code: -32000, message: "Failed to save merged cell: " <> err, data: Nothing }
              }
            Right _ -> pure $ Right
              { jsonrpc: "2.0"
              , id: req.id
              , result: Just $ AC.stringify $ encodeJson
                  { success: true
                  , mergedCell: encodeJson mergedCell
                  , regionId: regionId
                  }
              , error: Nothing
              }
        _, _ -> pure $ Right
          { jsonrpc: "2.0"
          , id: req.id
          , result: Nothing
          , error: Just { code: -32602, message: "Invalid cell data", data: Nothing }
          }
    Nothing -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32602, message: "Invalid params", data: Nothing }
      }

-- | Get replication status request
type ReplicationStatusRequest =
  { cellId :: String
  }

instance decodeJsonReplicationStatusRequest :: DecodeJson ReplicationStatusRequest where
  decodeJson json = do
    obj <- decodeJson json
    cellId <- obj .: "cellId"
    pure { cellId }

-- | Get replication status for a cell
-- | Endpoint: nexus.replication.status
nexusReplicationStatus :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusReplicationStatus req = do
  postgresPool <- getPostgresPool
  
  -- Parse params
  let parsedParams = case req.params of
        Just paramsStr -> case jsonParser paramsStr >>= decodeJson of
          Right p -> Just p
          Left _ -> Nothing
        Nothing -> Nothing
  
  case parsedParams of
    Just params -> do
      -- Load cell to get vector clock and region info
      loadResult <- launchAff $ Postgres.loadSemanticCell postgresPool params.cellId
      
      case loadResult of
        Left err -> pure $ Right
          { jsonrpc: "2.0"
          , id: req.id
          , result: Nothing
          , error: Just { code: -32000, message: "Failed to load cell: " <> err, data: Nothing }
          }
        Right (Just cellJson) -> do
          -- Parse cell to extract replication info
          case decodeJson cellJson of
            Right cell -> pure $ Right
              { jsonrpc: "2.0"
              , id: req.id
              , result: Just $ AC.stringify $ encodeJson
                  { cellId: params.cellId
                  , vectorClock: cell.vectorClock
                  , regionId: cell.regionId
                  , lastSyncedAt: cell.lastSyncedAt
                  }
              , error: Nothing
              }
            Left _ -> pure $ Right
              { jsonrpc: "2.0"
              , id: req.id
              , result: Nothing
              , error: Just { code: -32603, message: "Failed to parse cell", data: Nothing }
              }
        Right Nothing -> pure $ Right
          { jsonrpc: "2.0"
          , id: req.id
          , result: Nothing
          , error: Just { code: -32001, message: "Cell not found", data: Nothing }
          }
    Nothing -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32602, message: "Invalid params", data: Nothing }
      }
