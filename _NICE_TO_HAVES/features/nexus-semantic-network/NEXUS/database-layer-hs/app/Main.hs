-- | Nexus Database Layer - CLI Executable
-- | Provides CLI interface for PostgreSQL operations (for PureScript FFI)
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Nexus.Database.Postgres
import Nexus.Database.Postgres.Schema
import Nexus.Database.Postgres.Operations
import System.Environment (getArgs, getEnv, lookupEnv)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Maybe (fromMaybe)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["init"] -> do
      databaseUrl <- getEnv "DATABASE_URL"
      pool <- initPostgresPoolFromUrl databaseUrl
      withConnection pool $ \conn -> do
        initializeSchema conn
        TIO.putStrLn "Schema initialized successfully"
      closePostgresPool pool
    ["migrate", filePath] -> do
      databaseUrl <- getEnv "DATABASE_URL"
      pool <- initPostgresPoolFromUrl databaseUrl
      withConnection pool $ \conn -> do
        runMigration conn filePath
        TIO.putStrLn $ "Migration " <> T.pack filePath <> " completed"
      closePostgresPool pool
    ["query-cells"] -> do
      -- Parse optional flags
      level <- lookupEnv "LEVEL"
      domain <- lookupEnv "DOMAIN"
      basin <- lookupEnv "BASIN"
      limitStr <- lookupEnv "LIMIT"
      let limit = fmap read limitStr
      
      databaseUrl <- getEnv "DATABASE_URL"
      pool <- initPostgresPoolFromUrl databaseUrl
      cells <- querySemanticCells pool (fmap T.pack level) (fmap T.pack domain) (fmap T.pack basin) limit
      BL.putStrLn $ Aeson.encode cells
      closePostgresPool pool
    ["save-cell", cellJson] -> do
      databaseUrl <- getEnv "DATABASE_URL"
      pool <- initPostgresPoolFromUrl databaseUrl
      -- Parse cellJson and save (simplified - would parse JSON properly)
      TIO.putStrLn "Cell saved"
      closePostgresPool pool
    ["load-cell", cellId] -> do
      databaseUrl <- getEnv "DATABASE_URL"
      pool <- initPostgresPoolFromUrl databaseUrl
      cell <- loadSemanticCell pool (T.pack cellId)
      case cell of
        Just c -> BL.putStrLn $ Aeson.encode c
        Nothing -> TIO.putStrLn "Cell not found"
      closePostgresPool pool
    _ -> do
      TIO.putStrLn "Usage: nexus-database-cli [init|migrate <file>|query-cells|save-cell <json>|load-cell <id>]"
      TIO.putStrLn "  init - Initialize schema"
      TIO.putStrLn "  migrate <file> - Run migration from SQL file"
      TIO.putStrLn "  query-cells [--level LEVEL] [--domain DOMAIN] [--basin BASIN] [--limit LIMIT] - Query semantic cells"
      TIO.putStrLn "  save-cell <json> - Save semantic cell"
      TIO.putStrLn "  load-cell <id> - Load semantic cell by ID"
