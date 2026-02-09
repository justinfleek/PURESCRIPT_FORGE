-- | Nexus Database Layer - PostgreSQL Connection Pool
-- | PostgreSQL connection pool with Fly.io DATABASE_URL support
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}
module Nexus.Database.Postgres where

import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.URL (parseDatabaseUrl, DatabaseUrl(..))
import qualified Data.Pool as Pool
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import System.Environment (getEnv)
import Control.Exception (bracket, try, SomeException)
import Data.Maybe (fromMaybe)

-- | Database connection pool (opaque type for FFI)
data PostgresPool = PostgresPool (Pool.Pool Connection)

-- | Initialize PostgreSQL connection pool from DATABASE_URL
-- | Reads DATABASE_URL from environment (set by Fly.io)
-- | Format: postgres://user:password@host:port/database
initPostgresPool :: IO PostgresPool
initPostgresPool = do
  databaseUrl <- getEnv "DATABASE_URL"
  -- Parse connection string: postgres://user:pass@host:port/dbname
  case parseDatabaseUrl (T.pack databaseUrl) of
    Just connInfo -> do
      -- Create connection pool: 1-10 connections, 20 second timeout
      pool <- Pool.createPool (connect connInfo) close 1 10 20
      return (PostgresPool pool)
    Nothing -> error $ "Failed to parse DATABASE_URL: " ++ databaseUrl

-- | Initialize PostgreSQL connection pool from explicit connection string
-- | Format: postgres://user:password@host:port/database
initPostgresPoolFromUrl :: String -> IO PostgresPool
initPostgresPoolFromUrl databaseUrl = do
  case parseDatabaseUrl (T.pack databaseUrl) of
    Just connInfo -> do
      pool <- Pool.createPool (connect connInfo) close 1 10 20
      return (PostgresPool pool)
    Nothing -> error $ "Failed to parse database URL: " ++ databaseUrl

-- | Get connection from pool (for use in operations)
withConnection :: PostgresPool -> (Connection -> IO a) -> IO a
withConnection (PostgresPool pool) action = Pool.withResource pool action

-- | Execute query with connection from pool
executeQuery :: PostgresPool -> Query -> [Action] -> IO Int
executeQuery pool (Query q) params = withConnection pool $ \conn ->
  execute conn (Query q) params

-- | Execute query and return results
queryWith :: (FromRow r) => PostgresPool -> Query -> [Action] -> IO [r]
queryWith pool (Query q) params = withConnection pool $ \conn ->
  query conn (Query q) params

-- | Execute query and return single result (or Nothing)
queryOne :: (FromRow r) => PostgresPool -> Query -> [Action] -> IO (Maybe r)
queryOne pool query params = do
  results <- queryWith pool query params
  case results of
    [] -> return Nothing
    (r:_) -> return (Just r)

-- | Execute query and return single result (or error)
queryOneOrError :: (FromRow r) => PostgresPool -> Query -> [Action] -> String -> IO r
queryOneOrError pool query params errorMsg = do
  result <- queryOne pool query params
  case result of
    Nothing -> error errorMsg
    Just r -> return r

-- | Run transaction with connection from pool
withTransaction :: PostgresPool -> (Connection -> IO a) -> IO a
withTransaction pool action = withConnection pool $ \conn ->
  withTransaction conn action

-- | Close connection pool
closePostgresPool :: PostgresPool -> IO ()
closePostgresPool (PostgresPool pool) = Pool.destroyAllResources pool

-- Note: FFI bindings will be created via PureScript FFI pattern
-- (similar to bridge-database-hs CLI executable pattern)
