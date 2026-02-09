-- | Nexus Database Layer - PostgreSQL Operations
-- | CRUD operations for semantic cells, couplings, agents, etc.
{-# LANGUAGE OverloadedStrings #-}
module Nexus.Database.Postgres.Operations where

import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.FromRow
import Database.PostgreSQL.Simple.ToRow
import Database.PostgreSQL.Simple.Types (Only(..))
import qualified Data.Aeson as Aeson
import qualified Data.Text as T
import Data.Time.Clock (UTCTime)
import Data.Maybe (Maybe, catMaybes)
import Nexus.Database.Postgres

-- | Semantic cell record
data SemanticCellRecord = SemanticCellRecord
  { cellId :: T.Text
  , cellName :: T.Text
  , cellDescription :: T.Text
  , cellLevel :: T.Text
  , cellDomain :: T.Text
  , cellBasin :: T.Text
  , cellState :: Aeson.Value  -- JSONB CellState
  , cellParentId :: Maybe T.Text
  , cellChildrenIds :: Aeson.Value  -- JSONB array
  , cellCouplingIds :: Aeson.Value  -- JSONB array
  , cellCreatedAt :: UTCTime
  , cellUpdatedAt :: UTCTime
  , cellVectorClock :: Maybe Aeson.Value  -- JSONB vector clock
  , cellRegionId :: Maybe T.Text
  , cellLastSyncedAt :: Maybe UTCTime
  }

instance FromRow SemanticCellRecord where
  fromRow = SemanticCellRecord
    <$> field
    <*> field
    <*> field
    <*> field
    <*> field
    <*> field
    <*> field
    <*> field
    <*> field
    <*> field
    <*> field
    <*> field
    <*> field
    <*> field
    <*> field

-- | Save semantic cell
saveSemanticCell :: PostgresPool -> SemanticCellRecord -> IO ()
saveSemanticCell pool cell = withConnection pool $ \conn ->
  execute conn
    "INSERT INTO semantic_cells (id, name, description, level, domain, basin, state, parent_id, children_ids, coupling_ids, created_at, updated_at, vector_clock, region_id, last_synced_at) VALUES ($1, $2, $3, $4, $5, $6, $7::jsonb, $8, $9::jsonb, $10::jsonb, $11, $12, $13::jsonb, $14, $15) ON CONFLICT (id) DO UPDATE SET name = EXCLUDED.name, description = EXCLUDED.description, level = EXCLUDED.level, domain = EXCLUDED.domain, basin = EXCLUDED.basin, state = EXCLUDED.state, parent_id = EXCLUDED.parent_id, children_ids = EXCLUDED.children_ids, coupling_ids = EXCLUDED.coupling_ids, updated_at = EXCLUDED.updated_at, vector_clock = EXCLUDED.vector_clock, region_id = EXCLUDED.region_id, last_synced_at = EXCLUDED.last_synced_at"
    (cellId cell, cellName cell, cellDescription cell, cellLevel cell, cellDomain cell, cellBasin cell, Aeson.encode (cellState cell), cellParentId cell, Aeson.encode (cellChildrenIds cell), Aeson.encode (cellCouplingIds cell), cellCreatedAt cell, cellUpdatedAt cell, fmap Aeson.encode (cellVectorClock cell), cellRegionId cell, cellLastSyncedAt cell)

-- | Load semantic cell by ID
loadSemanticCell :: PostgresPool -> T.Text -> IO (Maybe SemanticCellRecord)
loadSemanticCell pool cellId = queryOne pool
    (Query "SELECT id, name, description, level, domain, basin, state, parent_id, children_ids, coupling_ids, created_at, updated_at, vector_clock, region_id, last_synced_at FROM semantic_cells WHERE id = $1")
    [Only cellId]

-- | Query semantic cells with filters
querySemanticCells :: PostgresPool -> Maybe T.Text -> Maybe T.Text -> Maybe T.Text -> Maybe Int -> IO [SemanticCellRecord]
querySemanticCells pool mLevel mDomain mBasin mLimit = withConnection pool $ \conn -> do
  -- Build query with conditional WHERE clauses
  -- PostgreSQL uses $1, $2, ... for parameters
  -- Build parameters list first, then construct query with correct numbering
  let paramsList = catMaybes [mLevel, mDomain, mBasin, fmap (T.pack . show) mLimit]
  let paramCount = length paramsList
  
  -- Build WHERE clauses with correct parameter numbers
  let (levelClause, paramIdx1) = case mLevel of
        Just _ -> (" AND level = $1", 1)
        Nothing -> ("", 0)
  let (domainClause, paramIdx2) = case mDomain of
        Just _ -> (" AND domain = $" <> T.pack (show (paramIdx1 + 1)), paramIdx1 + 1)
        Nothing -> ("", paramIdx1)
  let (basinClause, paramIdx3) = case mBasin of
        Just _ -> (" AND basin = $" <> T.pack (show (paramIdx2 + 1)), paramIdx2 + 1)
        Nothing -> ("", paramIdx2)
  let (limitClause, _) = case mLimit of
        Just _ -> (" LIMIT $" <> T.pack (show (paramIdx3 + 1)), paramIdx3 + 1)
        Nothing -> ("", paramIdx3)
  
  let baseQuery = "SELECT id, name, description, level, domain, basin, state, parent_id, children_ids, coupling_ids, created_at, updated_at, vector_clock, region_id, last_synced_at FROM semantic_cells WHERE 1=1"
  let queryStr = T.concat [baseQuery, levelClause, domainClause, basinClause, " ORDER BY updated_at DESC", limitClause]
  
  -- Convert parameters to Only wrappers
  let params = map Only paramsList
  
  query conn (Query queryStr) params

-- | Query semantic cells by ID prefix (for agent-specific queries)
-- | Uses PostgreSQL LIKE operator: WHERE id LIKE 'prefix%'
querySemanticCellsByPrefix :: PostgresPool -> T.Text -> Maybe Int -> IO [SemanticCellRecord]
querySemanticCellsByPrefix pool prefix mLimit = withConnection pool $ \conn -> do
  let prefixPattern = prefix <> "%"
  let queryStr = case mLimit of
        Just limit -> "SELECT id, name, description, level, domain, basin, state, parent_id, children_ids, coupling_ids, created_at, updated_at, vector_clock, region_id, last_synced_at FROM semantic_cells WHERE id LIKE $1 ORDER BY updated_at DESC LIMIT $2"
        Nothing -> "SELECT id, name, description, level, domain, basin, state, parent_id, children_ids, coupling_ids, created_at, updated_at, vector_clock, region_id, last_synced_at FROM semantic_cells WHERE id LIKE $1 ORDER BY updated_at DESC"
  case mLimit of
    Just limit -> query conn (Query queryStr) (prefixPattern, limit)
    Nothing -> query conn (Query queryStr) (Only prefixPattern)
