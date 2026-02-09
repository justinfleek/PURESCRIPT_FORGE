-- | Analytics Queries
-- | High-performance analytical queries using SQLite
-- | Note: Originally designed for DuckDB, now using SQLite for compatibility
{-# LANGUAGE OverloadedStrings #-}
module Bridge.Analytics.Queries
  ( queryTokenUsageByModel
  , queryCostTrends
  , queryTopSessionsByCost
  , queryModelPerformance
  , queryBalanceConsumption
  , queryDailySummary
  ) where

import Bridge.Analytics.DuckDB (AnalyticsDB(..))
import Database.SQLite.Simple (query, Only(..))
import Data.Text (Text)
import Data.Time (UTCTime)
import Data.Time.Format (formatTime, defaultTimeLocale)
import qualified Data.Text as T

-- | Format UTCTime for SQLite queries
formatUTC :: UTCTime -> String
formatUTC = formatTime defaultTimeLocale "%Y-%m-%d %H:%M:%S"

-- | Query: Token usage by model over time period
queryTokenUsageByModel :: AnalyticsDB -> UTCTime -> UTCTime -> IO [(Text, Integer, Double)]
queryTokenUsageByModel (AnalyticsDB conn) start end = do
  query conn
    "SELECT model, SUM(total_tokens) as tokens, SUM(cost_usd) as cost \
    \FROM message_metrics \
    \WHERE timestamp >= ? AND timestamp <= ? \
    \GROUP BY model \
    \ORDER BY tokens DESC"
    (formatUTC start, formatUTC end)

-- | Query: Cost trends over time (hourly)
queryCostTrends :: AnalyticsDB -> UTCTime -> UTCTime -> IO [(Text, Double)]
queryCostTrends (AnalyticsDB conn) start end = do
  query conn
    "SELECT hour, total_cost_usd \
    \FROM hourly_stats \
    \WHERE hour >= ? AND hour <= ? \
    \ORDER BY hour"
    (formatUTC start, formatUTC end)

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
    ()

-- | Query: Balance consumption rate
-- | Note: SQLite doesn't support LAG window function in all versions,
-- | so we use a subquery approach for compatibility
queryBalanceConsumption :: AnalyticsDB -> UTCTime -> UTCTime -> IO [(Text, Double, Double)]
queryBalanceConsumption (AnalyticsDB conn) start end = do
  query conn
    "SELECT \
    \  b1.timestamp, \
    \  b1.diem, \
    \  COALESCE((SELECT b2.diem FROM balance_history b2 \
    \            WHERE b2.timestamp < b1.timestamp \
    \            ORDER BY b2.timestamp DESC LIMIT 1) - b1.diem, 0) as consumed \
    \FROM balance_history b1 \
    \WHERE b1.timestamp >= ? AND b1.timestamp <= ? \
    \ORDER BY b1.timestamp"
    (formatUTC start, formatUTC end)

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
    (formatUTC start, formatUTC end)
