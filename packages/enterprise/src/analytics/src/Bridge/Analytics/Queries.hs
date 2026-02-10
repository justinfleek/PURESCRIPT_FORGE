{-# LANGUAGE OverloadedStrings #-}

-- | Bridge Analytics Queries
-- |
-- | Analytical query functions for the DuckDB-backed analytics engine.
-- | Provides token usage, cost trends, session rankings, model performance,
-- | balance consumption, and daily summary queries.
-- |
-- | Dependencies:
-- | - Bridge.Analytics.DuckDB: AnalyticsDB handle
-- | - Database.DuckDB.Simple: Query execution
-- | - Data.Text: Text handling
-- | - Data.Time: Time range parameters
module Bridge.Analytics.Queries where

import Bridge.Analytics.DuckDB (AnalyticsDB(..))
import Database.DuckDB.Simple (query)
import Data.Text (Text)
import Data.Time (UTCTime)

-- | Query token usage grouped by model
-- |
-- | Returns: [(model, total_prompt_tokens, total_completion_tokens, total_tokens, total_cost)]
queryTokenUsageByModel :: AnalyticsDB -> UTCTime -> UTCTime -> IO [(Text, Int, Int, Int, Double)]
queryTokenUsageByModel (AnalyticsDB conn) startTime endTime =
  query conn
    "SELECT model, \
    \SUM(prompt_tokens)::INTEGER, \
    \SUM(completion_tokens)::INTEGER, \
    \SUM(total_tokens)::INTEGER, \
    \SUM(cost) \
    \FROM message_metrics \
    \WHERE timestamp >= ? AND timestamp <= ? \
    \GROUP BY model \
    \ORDER BY SUM(cost) DESC"
    (startTime, endTime)

-- | Query cost trends over time (daily granularity)
-- |
-- | Returns: [(day, model, request_count, total_cost, avg_cost_per_request)]
queryCostTrends :: AnalyticsDB -> UTCTime -> UTCTime -> IO [(Text, Text, Int, Double, Double)]
queryCostTrends (AnalyticsDB conn) startTime endTime =
  query conn
    "SELECT CAST(day AS TEXT), model, \
    \request_count, total_cost, \
    \CASE WHEN request_count > 0 THEN total_cost / request_count ELSE 0.0 END \
    \FROM daily_stats \
    \WHERE day >= ? AND day <= ? \
    \ORDER BY day DESC, total_cost DESC"
    (startTime, endTime)

-- | Query top sessions by cost
-- |
-- | Returns: [(session_id, total_tokens, total_cost, request_count)]
queryTopSessionsByCost :: AnalyticsDB -> UTCTime -> UTCTime -> Int -> IO [(Text, Int, Double, Int)]
queryTopSessionsByCost (AnalyticsDB conn) startTime endTime limitN =
  query conn
    "SELECT session_id, \
    \SUM(total_tokens)::INTEGER, \
    \SUM(cost), \
    \COUNT(*)::INTEGER \
    \FROM message_metrics \
    \WHERE timestamp >= ? AND timestamp <= ? \
    \GROUP BY session_id \
    \ORDER BY SUM(cost) DESC \
    \LIMIT ?"
    (startTime, endTime, limitN)

-- | Query model performance metrics
-- |
-- | Returns: [(model, avg_prompt_tokens, avg_completion_tokens, avg_latency_ms, request_count)]
queryModelPerformance :: AnalyticsDB -> UTCTime -> UTCTime -> IO [(Text, Double, Double, Double, Int)]
queryModelPerformance (AnalyticsDB conn) startTime endTime =
  query conn
    "SELECT model, \
    \AVG(prompt_tokens), \
    \AVG(completion_tokens), \
    \AVG(latency_ms), \
    \COUNT(*)::INTEGER \
    \FROM message_metrics \
    \WHERE timestamp >= ? AND timestamp <= ? \
    \GROUP BY model \
    \ORDER BY COUNT(*) DESC"
    (startTime, endTime)

-- | Query balance consumption over time
-- |
-- | Returns: [(timestamp_text, diem, usd, effective, consumption_rate, time_to_depletion)]
queryBalanceConsumption :: AnalyticsDB -> UTCTime -> UTCTime -> IO [(Text, Double, Double, Double, Double, Maybe Int)]
queryBalanceConsumption (AnalyticsDB conn) startTime endTime =
  query conn
    "SELECT CAST(timestamp AS TEXT), \
    \diem, usd, effective, \
    \consumption_rate, time_to_depletion \
    \FROM balance_history \
    \WHERE timestamp >= ? AND timestamp <= ? \
    \ORDER BY timestamp ASC"
    (startTime, endTime)

-- | Query daily summary (combined metrics)
-- |
-- | Returns: [(day, total_requests, total_tokens, total_cost, unique_models, unique_sessions)]
queryDailySummary :: AnalyticsDB -> UTCTime -> UTCTime -> IO [(Text, Int, Int, Double, Int, Int)]
queryDailySummary (AnalyticsDB conn) startTime endTime =
  query conn
    "SELECT CAST(date_trunc('day', timestamp) AS TEXT), \
    \COUNT(*)::INTEGER, \
    \SUM(total_tokens)::INTEGER, \
    \SUM(cost), \
    \COUNT(DISTINCT model)::INTEGER, \
    \COUNT(DISTINCT session_id)::INTEGER \
    \FROM message_metrics \
    \WHERE timestamp >= ? AND timestamp <= ? \
    \GROUP BY date_trunc('day', timestamp) \
    \ORDER BY date_trunc('day', timestamp) DESC"
    (startTime, endTime)
