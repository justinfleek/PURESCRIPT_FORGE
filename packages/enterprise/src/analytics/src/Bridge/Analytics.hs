-- | Bridge Analytics FFI Facade
-- |
-- | Top-level module providing JSON-based FFI wrappers around
-- | the DuckDB analytics engine. All functions accept and return
-- | Text (JSON strings) for easy interop with the Bridge server.
-- |
-- | Dependencies:
-- | - Bridge.Analytics.DuckDB: Core analytics engine
-- | - Bridge.Analytics.Queries: Query functions
-- | - Data.Aeson: JSON encoding/decoding
-- | - Data.Time: UTC time parsing
module Bridge.Analytics
  ( AnalyticsHandle(..)
  , openAnalytics
  , closeAnalytics
  , loadFromSQLiteFFI
  , queryTokenUsageByModelFFI
  , queryCostTrendsFFI
  , queryTopSessionsByCostFFI
  , queryModelPerformanceFFI
  , queryBalanceConsumptionFFI
  , queryDailySummaryFFI
  ) where

import Bridge.Analytics.DuckDB
  ( AnalyticsDB
  , openAnalyticsDB
  , closeAnalyticsDB
  , initializeAnalyticsSchema
  , loadFromSQLite
  )
import Bridge.Analytics.Queries
  ( queryTokenUsageByModel
  , queryCostTrends
  , queryTopSessionsByCost
  , queryModelPerformance
  , queryBalanceConsumption
  , queryDailySummary
  )
import Data.Aeson (encode, ToJSON, toJSON, object, (.=))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TLE
import Data.Time (UTCTime)
import Data.Time.Format (parseTimeM, defaultTimeLocale)

-- | Analytics handle (opaque wrapper for FFI boundary)
newtype AnalyticsHandle = AnalyticsHandle
  { analyticsDB :: AnalyticsDB
  }

-- | Open analytics engine
-- |
-- | Opens DuckDB at the given path and initializes the schema.
openAnalytics :: FilePath -> IO AnalyticsHandle
openAnalytics dbPath = do
  db <- openAnalyticsDB dbPath
  initializeAnalyticsSchema db
  pure (AnalyticsHandle db)

-- | Close analytics engine
closeAnalytics :: AnalyticsHandle -> IO ()
closeAnalytics (AnalyticsHandle db) = closeAnalyticsDB db

-- | Load data from SQLite (FFI wrapper)
loadFromSQLiteFFI :: AnalyticsHandle -> Text -> IO ()
loadFromSQLiteFFI (AnalyticsHandle db) sqlitePath =
  loadFromSQLite db (T.unpack sqlitePath)

-- | Helper: encode result to JSON Text
toJsonText :: ToJSON a => a -> Text
toJsonText = TL.toStrict . TLE.decodeUtf8 . encode

-- | Helper: parse UTC time from ISO 8601 string
-- |
-- | Tries 3 common formats:
-- | 1. "%Y-%m-%dT%H:%M:%S%QZ" (full ISO with Z)
-- | 2. "%Y-%m-%dT%H:%M:%S%Q" (ISO without Z)
-- | 3. "%Y-%m-%d %H:%M:%S" (space-separated)
parseUTCTime :: Text -> Maybe UTCTime
parseUTCTime txt =
  let s = T.unpack txt
  in case parseTimeM True defaultTimeLocale "%Y-%m-%dT%H:%M:%S%QZ" s of
    Just t -> Just t
    Nothing -> case parseTimeM True defaultTimeLocale "%Y-%m-%dT%H:%M:%S%Q" s of
      Just t -> Just t
      Nothing -> parseTimeM True defaultTimeLocale "%Y-%m-%d %H:%M:%S" s

-- | Query token usage by model (FFI wrapper)
-- |
-- | Accepts start/end as ISO timestamp Text, returns JSON array Text.
queryTokenUsageByModelFFI :: AnalyticsHandle -> Text -> Text -> IO Text
queryTokenUsageByModelFFI (AnalyticsHandle db) startText endText =
  case (parseUTCTime startText, parseUTCTime endText) of
    (Just start, Just end) -> do
      results <- queryTokenUsageByModel db start end
      let jsonRows = map (\(model, pt, ct, tt, cost) ->
            object [ "model" .= model
                   , "prompt_tokens" .= pt
                   , "completion_tokens" .= ct
                   , "total_tokens" .= tt
                   , "cost" .= cost
                   ]) results
      pure (toJsonText jsonRows)
    _ -> pure "{\"error\":\"Invalid time format\"}"

-- | Query cost trends (FFI wrapper)
queryCostTrendsFFI :: AnalyticsHandle -> Text -> Text -> IO Text
queryCostTrendsFFI (AnalyticsHandle db) startText endText =
  case (parseUTCTime startText, parseUTCTime endText) of
    (Just start, Just end) -> do
      results <- queryCostTrends db start end
      let jsonRows = map (\(day, model, count, cost, avgCost) ->
            object [ "day" .= day
                   , "model" .= model
                   , "request_count" .= count
                   , "total_cost" .= cost
                   , "avg_cost_per_request" .= avgCost
                   ]) results
      pure (toJsonText jsonRows)
    _ -> pure "{\"error\":\"Invalid time format\"}"

-- | Query top sessions by cost (FFI wrapper)
queryTopSessionsByCostFFI :: AnalyticsHandle -> Text -> Text -> Int -> IO Text
queryTopSessionsByCostFFI (AnalyticsHandle db) startText endText limitN =
  case (parseUTCTime startText, parseUTCTime endText) of
    (Just start, Just end) -> do
      results <- queryTopSessionsByCost db start end limitN
      let jsonRows = map (\(sessionId, tokens, cost, count) ->
            object [ "session_id" .= sessionId
                   , "total_tokens" .= tokens
                   , "total_cost" .= cost
                   , "request_count" .= count
                   ]) results
      pure (toJsonText jsonRows)
    _ -> pure "{\"error\":\"Invalid time format\"}"

-- | Query model performance (FFI wrapper)
queryModelPerformanceFFI :: AnalyticsHandle -> Text -> Text -> IO Text
queryModelPerformanceFFI (AnalyticsHandle db) startText endText =
  case (parseUTCTime startText, parseUTCTime endText) of
    (Just start, Just end) -> do
      results <- queryModelPerformance db start end
      let jsonRows = map (\(model, avgPt, avgCt, avgLat, count) ->
            object [ "model" .= model
                   , "avg_prompt_tokens" .= avgPt
                   , "avg_completion_tokens" .= avgCt
                   , "avg_latency_ms" .= avgLat
                   , "request_count" .= count
                   ]) results
      pure (toJsonText jsonRows)
    _ -> pure "{\"error\":\"Invalid time format\"}"

-- | Query balance consumption (FFI wrapper)
queryBalanceConsumptionFFI :: AnalyticsHandle -> Text -> Text -> IO Text
queryBalanceConsumptionFFI (AnalyticsHandle db) startText endText =
  case (parseUTCTime startText, parseUTCTime endText) of
    (Just start, Just end) -> do
      results <- queryBalanceConsumption db start end
      let jsonRows = map (\(ts, diem, usd, eff, rate, ttd) ->
            object [ "timestamp" .= ts
                   , "diem" .= diem
                   , "usd" .= usd
                   , "effective" .= eff
                   , "consumption_rate" .= rate
                   , "time_to_depletion" .= ttd
                   ]) results
      pure (toJsonText jsonRows)
    _ -> pure "{\"error\":\"Invalid time format\"}"

-- | Query daily summary (FFI wrapper)
queryDailySummaryFFI :: AnalyticsHandle -> Text -> Text -> IO Text
queryDailySummaryFFI (AnalyticsHandle db) startText endText =
  case (parseUTCTime startText, parseUTCTime endText) of
    (Just start, Just end) -> do
      results <- queryDailySummary db start end
      let jsonRows = map (\(day, requests, tokens, cost, models, sessions) ->
            object [ "day" .= day
                   , "total_requests" .= requests
                   , "total_tokens" .= tokens
                   , "total_cost" .= cost
                   , "unique_models" .= models
                   , "unique_sessions" .= sessions
                   ]) results
      pure (toJsonText jsonRows)
    _ -> pure "{\"error\":\"Invalid time format\"}"
