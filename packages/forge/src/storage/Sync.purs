-- | Database Sync Module - Periodic SQLite to DuckDB Synchronization
-- |
-- | Provides periodic synchronization from SQLite (operational database)
-- | to DuckDB (analytics database). Enables fast analytics queries on
-- | historical data without impacting operational database performance.
-- |
-- | Dependencies:
-- | - Bridge.FFI.Haskell.Database: SQLite database access
-- | - Bridge.FFI.Haskell.Analytics: DuckDB analytics access
-- | - Bridge.FFI.Node.Pino: Structured logging
module Bridge.Database.Sync where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, launchAff_, delay, Milliseconds(..))
import Effect.Class (liftEffect)
import Effect.Ref (Ref, new, read, write)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Bridge.FFI.Node.Pino as Pino
import Bridge.FFI.Haskell.Database as SQLite
import Bridge.FFI.Haskell.Analytics as DuckDB

-- | Sync configuration
-- |
-- | Configuration for periodic database synchronization.
type SyncConfig =
  { intervalMinutes :: Int
  , sqlitePath :: String
  , duckdbPath :: String
  }

-- | Sync state
type SyncState =
  { lastSyncTime :: Maybe Int -- Unix timestamp
  , syncInProgress :: Boolean
  , errorCount :: Int
  }

-- | Create sync state - Initialize sync state
-- |
-- | Creates a new sync state with default values (no sync performed yet).
createSyncState :: Effect (Ref SyncState)
createSyncState = new
  { lastSyncTime: Nothing
  , syncInProgress: false
  , errorCount: 0
  }

-- | Perform sync from SQLite to DuckDB
syncDatabases :: SQLite.DatabaseHandle -> DuckDB.AnalyticsHandle -> String -> String -> Pino.Logger -> Aff Unit
syncDatabases _sqliteHandle duckdbHandle sqlitePath _duckdbPath logger = do
  liftEffect $ Pino.info logger "Starting database sync"

  -- Load data from SQLite into DuckDB
  DuckDB.loadFromSQLite duckdbHandle sqlitePath

  liftEffect $ Pino.info logger "Database sync completed"

-- | Start periodic sync - Begin background sync loop
-- |
-- | Starts a background loop that periodically synchronizes SQLite to
-- | DuckDB at the configured interval.
startPeriodicSync :: SyncConfig -> SQLite.DatabaseHandle -> DuckDB.AnalyticsHandle -> Pino.Logger -> Ref SyncState -> Effect Unit
startPeriodicSync config sqliteHandle duckdbHandle logger stateRef = do
  launchAff_ $ syncLoop config sqliteHandle duckdbHandle logger stateRef

-- | Sync loop
syncLoop :: SyncConfig -> SQLite.DatabaseHandle -> DuckDB.AnalyticsHandle -> Pino.Logger -> Ref SyncState -> Aff Unit
syncLoop config sqliteHandle duckdbHandle logger stateRef = do
  -- Wait for interval
  delay (Milliseconds (toNumber config.intervalMinutes * 60.0 * 1000.0))

  -- Check if sync already in progress
  state <- liftEffect $ read stateRef
  if state.syncInProgress then do
    liftEffect $ Pino.warn logger "Sync already in progress, skipping"
    syncLoop config sqliteHandle duckdbHandle logger stateRef
  else do
    -- Mark sync in progress
    liftEffect $ write stateRef state { syncInProgress = true }

    -- Perform sync
    syncResult <- trySync (syncDatabases sqliteHandle duckdbHandle config.sqlitePath config.duckdbPath logger)

    case syncResult of
      Right _ -> do
        -- Update last sync time
        currentTime <- liftEffect getCurrentTimeMillis
        liftEffect $ write stateRef
          { lastSyncTime: Just currentTime
          , syncInProgress: false
          , errorCount: 0
          }
        liftEffect $ Pino.info logger "Periodic sync completed successfully"
      Left _err -> do
        -- Increment error count
        state' <- liftEffect $ read stateRef
        liftEffect $ write stateRef
          { lastSyncTime: state'.lastSyncTime
          , syncInProgress: false
          , errorCount: state'.errorCount + 1
          }
        liftEffect $ Pino.error logger "Periodic sync failed"

    -- Continue loop
    syncLoop config sqliteHandle duckdbHandle logger stateRef

-- | Convert Int to Number
toNumber :: Int -> Number
toNumber = toNumber'

foreign import toNumber' :: Int -> Number

-- | Get current time in milliseconds (Unix timestamp)
foreign import getCurrentTimeMillis :: Effect Int

-- | Try/catch for Aff
foreign import trySync :: forall a. Aff a -> Aff (Either String a)
