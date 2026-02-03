-- | Database Sync Module - Periodic SQLite to DuckDB Synchronization
-- |
-- | **What:** Provides periodic synchronization from SQLite (operational database)
-- |         to DuckDB (analytics database). Enables fast analytics queries on
-- |         historical data without impacting operational database performance.
-- | **Why:** Separates operational database (SQLite) from analytics database (DuckDB),
-- |         allowing fast analytical queries without affecting real-time operations.
-- |         Periodic sync ensures analytics data is up-to-date.
-- | **How:** Runs a background loop that periodically loads data from SQLite into
-- |         DuckDB. Tracks sync state to prevent concurrent syncs and handle errors.
-- |
-- | **Dependencies:**
-- | - `Bridge.FFI.Haskell.Database`: SQLite database access
-- | - `Bridge.FFI.Haskell.Analytics`: DuckDB analytics access
-- | - `Bridge.FFI.Node.Pino`: Structured logging
-- |
-- | **Mathematical Foundation:**
-- | - **Sync Interval:** Sync runs every `intervalMinutes` minutes.
-- | - **Sync State:** Tracks `lastSyncTime`, `syncInProgress`, and `errorCount`.
-- | - **Concurrency:** Only one sync runs at a time (enforced by `syncInProgress` flag).
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Database.Sync as Sync
-- |
-- | -- Create sync state
-- | syncState <- Sync.createSyncState
-- |
-- | -- Start periodic sync
-- | Sync.startPeriodicSync syncConfig sqliteHandle duckdbHandle logger syncState
-- | ```
module Bridge.Database.Sync where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, launchAff_, delay, Milliseconds(..))
import Effect.Class (liftEffect)
import Effect.Ref (Ref, new, read, write)
import Data.Maybe (Maybe(..))
import Bridge.FFI.Node.Pino as Pino
import Bridge.FFI.Haskell.Database as SQLite
import Bridge.FFI.Haskell.Analytics as DuckDB

-- | Sync configuration - Database sync configuration
-- |
-- | **Purpose:** Configuration for periodic database synchronization.
-- | **Fields:**
-- | - `intervalMinutes`: Sync interval in minutes
-- | - `sqlitePath`: Path to SQLite database
-- | - `duckdbPath`: Path to DuckDB database
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
-- | **Purpose:** Creates a new sync state with default values (no sync performed yet).
-- | **Returns:** Mutable reference to SyncState
-- | **Side Effects:** Creates mutable reference
createSyncState :: Effect (Ref SyncState)
createSyncState = new
  { lastSyncTime: Nothing
  , syncInProgress: false
  , errorCount: 0
  }

-- | Perform sync from SQLite to DuckDB
syncDatabases :: SQLite.DatabaseHandle -> DuckDB.AnalyticsHandle -> String -> String -> Pino.Logger -> Aff Unit
syncDatabases sqliteHandle duckdbHandle sqlitePath duckdbPath logger = do
  liftEffect $ Pino.infoFields logger 
    "Starting database sync" 
    """{"sqlite":"\"""" <> sqlitePath <> "\"","duckdb":"\"""" <> duckdbPath <> "\"""}"""
  
  -- Load data from SQLite into DuckDB
  DuckDB.loadFromSQLite duckdbHandle sqlitePath
  
  liftEffect $ Pino.info logger "Database sync completed"

-- | Start periodic sync - Begin background sync loop
-- |
-- | **Purpose:** Starts a background loop that periodically synchronizes SQLite to
-- |             DuckDB at the configured interval.
-- | **Parameters:**
-- | - `config`: Sync configuration (interval, paths)
-- | - `sqliteHandle`: SQLite database handle
-- | - `duckdbHandle`: DuckDB analytics handle
-- | - `logger`: Pino logger
-- | - `stateRef`: Mutable reference to sync state
-- | **Returns:** Unit
-- | **Side Effects:** Launches background Aff computation that runs indefinitely
-- |
-- | **Behavior:**
-- | - Waits for `intervalMinutes` before first sync
-- | - Performs sync, then waits for interval again
-- | - Skips sync if one is already in progress
-- | - Updates sync state after each sync (success or error)
startPeriodicSync :: SyncConfig -> SQLite.DatabaseHandle -> DuckDB.AnalyticsHandle -> Pino.Logger -> Ref SyncState -> Effect Unit
startPeriodicSync config sqliteHandle duckdbHandle logger stateRef = do
  launchAff_ $ syncLoop config sqliteHandle duckdbHandle logger stateRef

-- | Sync loop
syncLoop :: SyncConfig -> SQLite.DatabaseHandle -> DuckDB.AnalyticsHandle -> Pino.Logger -> Ref SyncState -> Aff Unit
syncLoop config sqliteHandle duckdbHandle logger stateRef = do
  -- Wait for interval
  delay (Milliseconds (config.intervalMinutes * 60 * 1000.0))
  
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
        currentTime <- liftEffect $ getCurrentTimeMillis
        liftEffect $ write stateRef 
          { lastSyncTime: Just currentTime
          , syncInProgress: false
          , errorCount: 0
          }
        liftEffect $ Pino.info logger "Periodic sync completed successfully"
      Left err -> do
        -- Increment error count
        state' <- liftEffect $ read stateRef
        liftEffect $ write stateRef 
          { lastSyncTime: state'.lastSyncTime
          , syncInProgress: false
          , errorCount: state'.errorCount + 1
          }
        liftEffect $ Pino.errorFields logger "Periodic sync failed"
          """{"error":"\"""" <> show err <> "\"""}"""
    
    -- Continue loop
    syncLoop config sqliteHandle duckdbHandle logger stateRef

-- | Get current time in milliseconds (Unix timestamp)
foreign import getCurrentTimeMillis :: Effect Int

-- | Try/catch for Aff
foreign import trySync :: forall a. Aff a -> Aff (Either String a)
