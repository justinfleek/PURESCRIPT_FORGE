-- | Nexus Database Layer - PostgreSQL Schema
-- | Schema initialization and migration functions
{-# LANGUAGE OverloadedStrings #-}
module Nexus.Database.Postgres.Schema where

import Database.PostgreSQL.Simple
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Control.Exception (bracket)
import System.IO (readFile)

-- | Initialize PostgreSQL schema
-- | Creates all tables, indexes, triggers, and functions
initializeSchema :: Connection -> IO ()
initializeSchema conn = do
  -- Read migration files
  migration1 <- readFile "NEXUS/database-layer/migrations/001_initial_postgres_schema.sql"
  migration2 <- readFile "NEXUS/database-layer/migrations/002_add_distributed_sync_columns.sql"
  
  -- Execute migrations
  execute_ conn (Query $ T.pack migration1)
  execute_ conn (Query $ T.pack migration2)
  
  -- Commit
  commit conn

-- | Run migration from SQL file
runMigration :: Connection -> FilePath -> IO ()
runMigration conn filePath = do
  migrationSQL <- readFile filePath
  execute_ conn (Query $ T.pack migrationSQL)
  commit conn

-- | Check if schema is initialized
schemaInitialized :: Connection -> IO Bool
schemaInitialized conn = do
  result <- query_ conn "SELECT EXISTS (SELECT FROM information_schema.tables WHERE table_name = 'semantic_cells')"
  case result of
    [Only exists] -> return exists
    _ -> return False
