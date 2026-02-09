-- | Analytics Database (SQLite-based)
-- | High-performance analytical queries for metrics and statistics
-- | Note: Originally designed for DuckDB, now using SQLite for compatibility
{-# LANGUAGE OverloadedStrings #-}
module Bridge.Analytics.DuckDB
  ( AnalyticsDB(..)
  , openAnalyticsDB
  , closeAnalyticsDB
  , initializeAnalyticsSchema
  , loadFromSQLite
  ) where

import Database.SQLite.Simple (Connection, open, close, execute_, execute, Query(..))
import Data.Text (Text)
import qualified Data.Text as T
import Data.String (fromString)

-- | Analytics database handle
data AnalyticsDB = AnalyticsDB Connection

-- | Open analytics database (in-memory or file-based)
openAnalyticsDB :: Maybe FilePath -> IO AnalyticsDB
openAnalyticsDB maybePath = do
  conn <- case maybePath of
    Just path -> open path
    Nothing -> open ":memory:" -- In-memory for performance
  initializeAnalyticsSchema conn
  return (AnalyticsDB conn)

-- | Close analytics database
closeAnalyticsDB :: AnalyticsDB -> IO ()
closeAnalyticsDB (AnalyticsDB conn) = close conn

-- | Initialize analytics schema
initializeAnalyticsSchema :: Connection -> IO ()
initializeAnalyticsSchema conn = do
  -- Create tables optimized for analytics
  execute_ conn "CREATE TABLE IF NOT EXISTS message_metrics (\
    \id INTEGER PRIMARY KEY,\
    \message_id TEXT NOT NULL,\
    \session_id TEXT NOT NULL,\
    \timestamp TEXT NOT NULL,\
    \model TEXT NOT NULL,\
    \provider TEXT NOT NULL,\
    \prompt_tokens INTEGER NOT NULL,\
    \completion_tokens INTEGER NOT NULL,\
    \cached_tokens INTEGER DEFAULT 0,\
    \total_tokens INTEGER NOT NULL,\
    \cost_usd REAL NOT NULL,\
    \diem_cost REAL,\
    \latency_ms INTEGER,\
    \duration_ms INTEGER,\
    \tokens_per_second REAL\
    \)"
  
  execute_ conn "CREATE TABLE IF NOT EXISTS hourly_stats (\
    \hour TEXT PRIMARY KEY,\
    \prompt_tokens INTEGER DEFAULT 0,\
    \completion_tokens INTEGER DEFAULT 0,\
    \total_tokens INTEGER DEFAULT 0,\
    \total_cost_usd REAL DEFAULT 0,\
    \message_count INTEGER DEFAULT 0,\
    \session_count INTEGER DEFAULT 0,\
    \diem_start REAL,\
    \diem_end REAL,\
    \diem_consumed REAL\
    \)"
  
  execute_ conn "CREATE TABLE IF NOT EXISTS daily_stats (\
    \day TEXT PRIMARY KEY,\
    \prompt_tokens INTEGER DEFAULT 0,\
    \completion_tokens INTEGER DEFAULT 0,\
    \total_tokens INTEGER DEFAULT 0,\
    \total_cost_usd REAL DEFAULT 0,\
    \message_count INTEGER DEFAULT 0,\
    \session_count INTEGER DEFAULT 0,\
    \tool_call_count INTEGER DEFAULT 0,\
    \diem_start REAL,\
    \diem_end REAL,\
    \diem_consumed REAL,\
    \by_model TEXT\
    \)"
  
  execute_ conn "CREATE TABLE IF NOT EXISTS balance_history (\
    \id INTEGER PRIMARY KEY,\
    \timestamp TEXT NOT NULL,\
    \diem REAL NOT NULL,\
    \usd REAL,\
    \effective REAL,\
    \source TEXT,\
    \message_id TEXT\
    \)"
  
  -- Create indexes for fast queries
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_message_metrics_session ON message_metrics(session_id)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_message_metrics_timestamp ON message_metrics(timestamp)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_message_metrics_model ON message_metrics(model)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_balance_history_timestamp ON balance_history(timestamp)"

-- | Load data from another SQLite database into analytics
-- | Note: SQLite doesn't support ATTACH with TYPE, so we use a different approach
-- | This function is a placeholder - actual implementation would use direct queries
loadFromSQLite :: AnalyticsDB -> FilePath -> IO ()
loadFromSQLite (AnalyticsDB conn) sqlitePath = do
  -- For SQLite-to-SQLite transfer, we need to attach the source database
  -- and copy data manually. SQLite supports ATTACH but without TYPE specifier.
  execute_ conn (Query $ "ATTACH DATABASE '" <> T.pack sqlitePath <> "' AS source_db")
  
  -- Copy message_metrics (with conflict handling)
  execute_ conn "INSERT OR REPLACE INTO message_metrics \
    \SELECT * FROM source_db.message_metrics \
    \WHERE EXISTS (SELECT 1 FROM source_db.sqlite_master WHERE type='table' AND name='message_metrics')"
  
  -- Copy hourly_stats
  execute_ conn "INSERT OR REPLACE INTO hourly_stats \
    \SELECT * FROM source_db.hourly_stats \
    \WHERE EXISTS (SELECT 1 FROM source_db.sqlite_master WHERE type='table' AND name='hourly_stats')"
  
  -- Copy daily_stats
  execute_ conn "INSERT OR REPLACE INTO daily_stats \
    \SELECT * FROM source_db.daily_stats \
    \WHERE EXISTS (SELECT 1 FROM source_db.sqlite_master WHERE type='table' AND name='daily_stats')"
  
  -- Copy balance_history
  execute_ conn "INSERT OR REPLACE INTO balance_history \
    \SELECT * FROM source_db.balance_history \
    \WHERE EXISTS (SELECT 1 FROM source_db.sqlite_master WHERE type='table' AND name='balance_history')"
  
  -- Detach source database
  execute_ conn "DETACH DATABASE source_db"
