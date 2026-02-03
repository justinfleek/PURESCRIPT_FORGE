-- | Analytics Queries
-- | High-performance analytical queries using DuckDB
{-# LANGUAGE OverloadedStrings #-}
module Bridge.Analytics.Queries where

import Bridge.Analytics.DuckDB (AnalyticsDB(..))
import Database.DuckDB.Simple (query, Only(..))
import Data.Text (Text)
import Data.Time (UTCTime)
import qualified Data.Text as T

-- | Query: Token usage by model over time period
queryTokenUsageByModel :: AnalyticsDB -> UTCTime -> UTCTime -> IO [(Text, Integer, Double)]
queryTokenUsageByModel (AnalyticsDB conn) start end = do
  query conn
    "SELECT model, SUM(total_tokens) as tokens, SUM(cost_usd) as cost \
    \FROM message_metrics \
    \WHERE timestamp >= ? AND timestamp <= ? \
    \GROUP BY model \
    \ORDER BY tokens DESC"
    (start, end)

-- | Query: Cost trends over time (hourly)
queryCostTrends :: AnalyticsDB -> UTCTime -> UTCTime -> IO [(UTCTime, Double)]
queryCostTrends (AnalyticsDB conn) start end = do
  query conn
    "SELECT hour, total_cost_usd \
    \FROM hourly_stats \
    \WHERE hour >= ? AND hour <= ? \
    \ORDER BY hour"
    (start, end)

-- | Query: Top sessions by cost
queryTopSessionsByCost :: AnalyticsDB -> Int -> IO [(Text, Double, Integer)]
queryTopSessionsByCost (AnalyticsDB conn) limit = do
  query conn
    "SELECT session_id, SUM(cost_usd) as total_cost, COUNT(*) as message_count \
    \FROM message_metrics \
    \GROUP BY session_id \
    \ORDER BY total_cost DESC \
    \LIMIT ?"
    (Only limit)

-- | Query: Model performance metrics
queryModelPerformance :: AnalyticsDB -> IO [(Text, Double, Double, Double)]
queryModelPerformance (AnalyticsDB conn) = do
  query conn
    "SELECT \
    \  model, \
    \  AVG(tokens_per_second) as avg_tps, \
    \  AVG(latency_ms) as avg_latency, \
    \  AVG(cost_usd) as avg_cost \
    \FROM message_metrics \
    \WHERE tokens_per_second IS NOT NULL \
    \GROUP BY model \
    \ORDER BY avg_tps DESC"

-- | Query: Balance consumption rate
queryBalanceConsumption :: AnalyticsDB -> UTCTime -> UTCTime -> IO [(UTCTime, Double, Double)]
queryBalanceConsumption (AnalyticsDB conn) start end = do
  query conn
    "SELECT \
    \  timestamp, \
    \  diem, \
    \  LAG(diem) OVER (ORDER BY timestamp) - diem as consumed \
    \FROM balance_history \
    \WHERE timestamp >= ? AND timestamp <= ? \
    \ORDER BY timestamp"
    (start, end)

-- | Query: Daily aggregation summary
queryDailySummary :: AnalyticsDB -> UTCTime -> UTCTime -> IO [(Text, Integer, Double, Integer)]
queryDailySummary (AnalyticsDB conn) start end = do
  query conn
    "SELECT \
    \  day, \
    \  SUM(total_tokens) as tokens, \
    \  SUM(total_cost_usd) as cost, \
    \  SUM(message_count) as messages \
    \FROM daily_stats \
    \WHERE day >= DATE(?) AND day <= DATE(?) \
    \GROUP BY day \
    \ORDER BY day DESC"
    (start, end)
