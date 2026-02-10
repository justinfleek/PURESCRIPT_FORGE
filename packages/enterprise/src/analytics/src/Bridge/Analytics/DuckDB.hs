{-# LANGUAGE OverloadedStrings #-}

-- | Bridge Analytics DuckDB
-- |
-- | DuckDB-based analytics engine for aggregating and querying
-- | token usage, cost trends, and balance history metrics.
-- | Loads data from the primary SQLite database into DuckDB
-- | for fast OLAP-style queries.
-- |
-- | Dependencies:
-- | - Database.DuckDB.Simple: DuckDB connection and queries
-- | - Data.Text: Text handling
module Bridge.Analytics.DuckDB where

import Database.DuckDB.Simple (Connection, open, close, execute_)
import Data.Text (Text)
import qualified Data.Text as T

-- | Analytics database handle (wraps DuckDB connection)
newtype AnalyticsDB = AnalyticsDB
  { analyticsConnection :: Connection
  }

-- | Open analytics database
-- |
-- | Opens a DuckDB database at the given file path.
-- | Use ":memory:" for in-memory analytics.
openAnalyticsDB :: FilePath -> IO AnalyticsDB
openAnalyticsDB dbPath = do
  conn <- open dbPath
  pure (AnalyticsDB conn)

-- | Close analytics database
closeAnalyticsDB :: AnalyticsDB -> IO ()
closeAnalyticsDB (AnalyticsDB conn) = close conn

-- | Initialize analytics schema
-- |
-- | Creates the 4 core analytics tables:
-- | - message_metrics: Per-message token usage and cost
-- | - hourly_stats: Aggregated hourly statistics
-- | - daily_stats: Aggregated daily statistics
-- | - balance_history: Balance snapshots over time
initializeAnalyticsSchema :: AnalyticsDB -> IO ()
initializeAnalyticsSchema (AnalyticsDB conn) = do
  -- Message-level metrics
  execute_ conn "CREATE TABLE IF NOT EXISTS message_metrics (\
    \id TEXT PRIMARY KEY,\
    \session_id TEXT NOT NULL,\
    \model TEXT NOT NULL,\
    \provider TEXT NOT NULL,\
    \prompt_tokens INTEGER NOT NULL,\
    \completion_tokens INTEGER NOT NULL,\
    \total_tokens INTEGER NOT NULL,\
    \cost DOUBLE NOT NULL,\
    \latency_ms INTEGER,\
    \timestamp TIMESTAMP NOT NULL\
    \)"

  -- Hourly aggregated statistics
  execute_ conn "CREATE TABLE IF NOT EXISTS hourly_stats (\
    \hour TIMESTAMP NOT NULL,\
    \model TEXT NOT NULL,\
    \provider TEXT NOT NULL,\
    \request_count INTEGER NOT NULL DEFAULT 0,\
    \total_prompt_tokens BIGINT NOT NULL DEFAULT 0,\
    \total_completion_tokens BIGINT NOT NULL DEFAULT 0,\
    \total_tokens BIGINT NOT NULL DEFAULT 0,\
    \total_cost DOUBLE NOT NULL DEFAULT 0.0,\
    \avg_latency_ms DOUBLE,\
    \PRIMARY KEY (hour, model, provider)\
    \)"

  -- Daily aggregated statistics
  execute_ conn "CREATE TABLE IF NOT EXISTS daily_stats (\
    \day DATE NOT NULL,\
    \model TEXT NOT NULL,\
    \provider TEXT NOT NULL,\
    \request_count INTEGER NOT NULL DEFAULT 0,\
    \total_prompt_tokens BIGINT NOT NULL DEFAULT 0,\
    \total_completion_tokens BIGINT NOT NULL DEFAULT 0,\
    \total_tokens BIGINT NOT NULL DEFAULT 0,\
    \total_cost DOUBLE NOT NULL DEFAULT 0.0,\
    \avg_latency_ms DOUBLE,\
    \peak_hour INTEGER,\
    \PRIMARY KEY (day, model, provider)\
    \)"

  -- Balance history snapshots
  execute_ conn "CREATE TABLE IF NOT EXISTS balance_history (\
    \id TEXT PRIMARY KEY,\
    \timestamp TIMESTAMP NOT NULL,\
    \diem DOUBLE NOT NULL,\
    \usd DOUBLE NOT NULL,\
    \effective DOUBLE NOT NULL,\
    \consumption_rate DOUBLE NOT NULL,\
    \time_to_depletion INTEGER\
    \)"

  -- Create indices for common query patterns
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_mm_session ON message_metrics(session_id)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_mm_model ON message_metrics(model)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_mm_timestamp ON message_metrics(timestamp)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_bh_timestamp ON balance_history(timestamp)"

-- | Load data from SQLite into DuckDB
-- |
-- | Attaches the SQLite database as a source and copies
-- | session records into the message_metrics table.
-- | Aggregates into hourly_stats and daily_stats.
loadFromSQLite :: AnalyticsDB -> FilePath -> IO ()
loadFromSQLite (AnalyticsDB conn) sqlitePath = do
  -- Attach SQLite database as external source
  let attachCmd = T.concat
        [ "INSTALL sqlite; LOAD sqlite; ATTACH '"
        , T.pack sqlitePath
        , "' AS sqlite_source (TYPE sqlite)"
        ]
  execute_ conn (T.unpack attachCmd)

  -- Load message metrics from sessions table
  execute_ conn "INSERT INTO message_metrics \
    \SELECT id, session_id, model, provider, \
    \prompt_tokens, completion_tokens, total_tokens, \
    \cost, NULL, started_at \
    \FROM sqlite_source.sessions \
    \WHERE id NOT IN (SELECT id FROM message_metrics)"

  -- Load balance history
  execute_ conn "INSERT INTO balance_history \
    \SELECT id, timestamp, diem, usd, effective, \
    \consumption_rate, time_to_depletion \
    \FROM sqlite_source.balance_history \
    \WHERE id NOT IN (SELECT id FROM balance_history)"

  -- Rebuild hourly stats
  execute_ conn "DELETE FROM hourly_stats"
  execute_ conn "INSERT INTO hourly_stats \
    \SELECT date_trunc('hour', timestamp) AS hour, \
    \model, provider, \
    \COUNT(*) AS request_count, \
    \SUM(prompt_tokens) AS total_prompt_tokens, \
    \SUM(completion_tokens) AS total_completion_tokens, \
    \SUM(total_tokens) AS total_tokens, \
    \SUM(cost) AS total_cost, \
    \AVG(latency_ms) AS avg_latency_ms \
    \FROM message_metrics \
    \GROUP BY hour, model, provider"

  -- Rebuild daily stats
  execute_ conn "DELETE FROM daily_stats"
  execute_ conn "INSERT INTO daily_stats \
    \SELECT date_trunc('day', timestamp) AS day, \
    \model, provider, \
    \COUNT(*) AS request_count, \
    \SUM(prompt_tokens) AS total_prompt_tokens, \
    \SUM(completion_tokens) AS total_completion_tokens, \
    \SUM(total_tokens) AS total_tokens, \
    \SUM(cost) AS total_cost, \
    \AVG(latency_ms) AS avg_latency_ms, \
    \EXTRACT(HOUR FROM timestamp) AS peak_hour \
    \FROM message_metrics \
    \GROUP BY day, model, provider, peak_hour"

  -- Detach SQLite source
  execute_ conn "DETACH sqlite_source"
