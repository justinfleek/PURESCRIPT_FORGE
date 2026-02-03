-- | DuckDB Analytics Database
-- | High-performance analytical queries for metrics and statistics
{-# LANGUAGE OverloadedStrings #-}
module Bridge.Analytics.DuckDB where

import Database.DuckDB.Simple (Connection, connect, close, execute_)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE

-- | Analytics database handle
data AnalyticsDB = AnalyticsDB Connection

-- | Open analytics database (in-memory or file-based)
openAnalyticsDB :: Maybe FilePath -> IO AnalyticsDB
openAnalyticsDB maybePath = do
  conn <- case maybePath of
    Just path -> connect path
    Nothing -> connect ":memory:" -- In-memory for performance
  initializeAnalyticsSchema conn
  return (AnalyticsDB conn)

-- | Close analytics database
closeAnalyticsDB :: AnalyticsDB -> IO ()
closeAnalyticsDB (AnalyticsDB conn) = close conn

-- | Initialize analytics schema
initializeAnalyticsSchema :: Connection -> IO ()
initializeAnalyticsSchema conn = do
  -- Create tables optimized for analytics
  execute conn "CREATE TABLE IF NOT EXISTS message_metrics (\
    \id BIGINT PRIMARY KEY,\
    \message_id TEXT NOT NULL,\
    \session_id TEXT NOT NULL,\
    \timestamp TIMESTAMP NOT NULL,\
    \model TEXT NOT NULL,\
    \provider TEXT NOT NULL,\
    \prompt_tokens INTEGER NOT NULL,\
    \completion_tokens INTEGER NOT NULL,\
    \cached_tokens INTEGER DEFAULT 0,\
    \total_tokens INTEGER NOT NULL,\
    \cost_usd DOUBLE NOT NULL,\
    \diem_cost DOUBLE,\
    \latency_ms INTEGER,\
    \duration_ms INTEGER,\
    \tokens_per_second DOUBLE\
    \)"
  
  execute_ conn "CREATE TABLE IF NOT EXISTS hourly_stats (\
    \hour TIMESTAMP PRIMARY KEY,\
    \prompt_tokens BIGINT DEFAULT 0,\
    \completion_tokens BIGINT DEFAULT 0,\
    \total_tokens BIGINT DEFAULT 0,\
    \total_cost_usd DOUBLE DEFAULT 0,\
    \message_count INTEGER DEFAULT 0,\
    \session_count INTEGER DEFAULT 0,\
    \diem_start DOUBLE,\
    \diem_end DOUBLE,\
    \diem_consumed DOUBLE\
    \)"
  
  execute_ conn "CREATE TABLE IF NOT EXISTS daily_stats (\
    \day DATE PRIMARY KEY,\
    \prompt_tokens BIGINT DEFAULT 0,\
    \completion_tokens BIGINT DEFAULT 0,\
    \total_tokens BIGINT DEFAULT 0,\
    \total_cost_usd DOUBLE DEFAULT 0,\
    \message_count INTEGER DEFAULT 0,\
    \session_count INTEGER DEFAULT 0,\
    \tool_call_count INTEGER DEFAULT 0,\
    \diem_start DOUBLE,\
    \diem_end DOUBLE,\
    \diem_consumed DOUBLE,\
    \by_model TEXT\
    \)"
  
  execute_ conn "CREATE TABLE IF NOT EXISTS balance_history (\
    \id BIGINT PRIMARY KEY,\
    \timestamp TIMESTAMP NOT NULL,\
    \diem DOUBLE NOT NULL,\
    \usd DOUBLE,\
    \effective DOUBLE,\
    \source TEXT,\
    \message_id TEXT\
    \)"
  
  -- Create indexes for fast queries
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_message_metrics_session ON message_metrics(session_id)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_message_metrics_timestamp ON message_metrics(timestamp)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_message_metrics_model ON message_metrics(model)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_balance_history_timestamp ON balance_history(timestamp)"

-- | Load data from SQLite into DuckDB for analytics
loadFromSQLite :: AnalyticsDB -> FilePath -> IO ()
loadFromSQLite (AnalyticsDB conn) sqlitePath = do
  -- Attach SQLite database
  execute_ conn $ "ATTACH '" <> T.pack sqlitePath <> "' AS sqlite_db (TYPE SQLITE)"
  
  -- Copy data from SQLite to DuckDB (use INSERT OR IGNORE for DuckDB compatibility)
  execute_ conn "INSERT INTO message_metrics \
    \SELECT * FROM sqlite_db.message_metrics \
    \ON CONFLICT (id) DO UPDATE SET \
    \  message_id = EXCLUDED.message_id, \
    \  session_id = EXCLUDED.session_id, \
    \  timestamp = EXCLUDED.timestamp, \
    \  model = EXCLUDED.model, \
    \  provider = EXCLUDED.provider, \
    \  prompt_tokens = EXCLUDED.prompt_tokens, \
    \  completion_tokens = EXCLUDED.completion_tokens, \
    \  cached_tokens = EXCLUDED.cached_tokens, \
    \  total_tokens = EXCLUDED.total_tokens, \
    \  cost_usd = EXCLUDED.cost_usd, \
    \  diem_cost = EXCLUDED.diem_cost, \
    \  latency_ms = EXCLUDED.latency_ms, \
    \  duration_ms = EXCLUDED.duration_ms, \
    \  tokens_per_second = EXCLUDED.tokens_per_second"
  
  execute_ conn "INSERT INTO hourly_stats \
    \SELECT * FROM sqlite_db.hourly_stats \
    \ON CONFLICT (hour) DO UPDATE SET \
    \  prompt_tokens = EXCLUDED.prompt_tokens, \
    \  completion_tokens = EXCLUDED.completion_tokens, \
    \  total_tokens = EXCLUDED.total_tokens, \
    \  total_cost_usd = EXCLUDED.total_cost_usd, \
    \  message_count = EXCLUDED.message_count, \
    \  session_count = EXCLUDED.session_count, \
    \  diem_start = EXCLUDED.diem_start, \
    \  diem_end = EXCLUDED.diem_end, \
    \  diem_consumed = EXCLUDED.diem_consumed"
  
  execute_ conn "INSERT INTO daily_stats \
    \SELECT * FROM sqlite_db.daily_stats \
    \ON CONFLICT (day) DO UPDATE SET \
    \  prompt_tokens = EXCLUDED.prompt_tokens, \
    \  completion_tokens = EXCLUDED.completion_tokens, \
    \  total_tokens = EXCLUDED.total_tokens, \
    \  total_cost_usd = EXCLUDED.total_cost_usd, \
    \  message_count = EXCLUDED.message_count, \
    \  session_count = EXCLUDED.session_count, \
    \  tool_call_count = EXCLUDED.tool_call_count, \
    \  diem_start = EXCLUDED.diem_start, \
    \  diem_end = EXCLUDED.diem_end, \
    \  diem_consumed = EXCLUDED.diem_consumed, \
    \  by_model = EXCLUDED.by_model"
  
  execute_ conn "INSERT INTO balance_history \
    \SELECT * FROM sqlite_db.balance_history \
    \ON CONFLICT (id) DO UPDATE SET \
    \  timestamp = EXCLUDED.timestamp, \
    \  diem = EXCLUDED.diem, \
    \  usd = EXCLUDED.usd, \
    \  effective = EXCLUDED.effective, \
    \  source = EXCLUDED.source, \
    \  message_id = EXCLUDED.message_id"
  
  -- Detach SQLite database
  execute_ conn "DETACH sqlite_db"
