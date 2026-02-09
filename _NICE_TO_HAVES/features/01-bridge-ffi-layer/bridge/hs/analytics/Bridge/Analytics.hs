-- | Analytics Module
-- | Main analytics interface for Bridge Server
{-# LANGUAGE ForeignFunctionInterface #-}
module Bridge.Analytics where

import Bridge.Analytics.DuckDB
import Bridge.Analytics.Queries
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TLE
import Data.Aeson (encode)
import Data.Time.Format (parseTimeM, defaultTimeLocale)
import Data.Time.Clock (UTCTime)

-- | Analytics handle
data AnalyticsHandle = AnalyticsHandle AnalyticsDB

-- | Open analytics database
openAnalytics :: Maybe FilePath -> IO AnalyticsHandle
openAnalytics path = AnalyticsHandle <$> openAnalyticsDB path

-- | Close analytics database
closeAnalytics :: AnalyticsHandle -> IO ()
closeAnalytics (AnalyticsHandle db) = closeAnalyticsDB db

-- | Load data from SQLite
loadFromSQLiteFFI :: AnalyticsHandle -> FilePath -> IO ()
loadFromSQLiteFFI (AnalyticsHandle db) = loadFromSQLite db

-- | Query token usage by model
queryTokenUsageByModelFFI :: AnalyticsHandle -> Text -> Text -> IO Text
queryTokenUsageByModelFFI (AnalyticsHandle db) start end = do
  startResult <- parseUTCTime (T.unpack start)
  endResult <- parseUTCTime (T.unpack end)
  case (startResult, endResult) of
    (Left err, _) -> return (T.pack ("Error: " ++ err))
    (_, Left err) -> return (T.pack ("Error: " ++ err))
    (Right start', Right end') -> do
      result <- queryTokenUsageByModel db start' end'
      return (TL.toStrict (TLE.decodeUtf8 (encode result)))

-- | Query cost trends
queryCostTrendsFFI :: AnalyticsHandle -> Text -> Text -> IO Text
queryCostTrendsFFI (AnalyticsHandle db) start end = do
  startResult <- parseUTCTime (T.unpack start)
  endResult <- parseUTCTime (T.unpack end)
  case (startResult, endResult) of
    (Left err, _) -> return (T.pack ("Error: " ++ err))
    (_, Left err) -> return (T.pack ("Error: " ++ err))
    (Right start', Right end') -> do
      result <- queryCostTrends db start' end'
      return (TL.toStrict (TLE.decodeUtf8 (encode result)))

-- | Query top sessions by cost (FFI-friendly)
queryTopSessionsByCostFFI :: AnalyticsHandle -> Int -> IO Text
queryTopSessionsByCostFFI (AnalyticsHandle db) limit = do
  result <- queryTopSessionsByCost db limit
  return (TL.toStrict (TLE.decodeUtf8 (encode result)))

-- | Query model performance
queryModelPerformanceFFI :: AnalyticsHandle -> IO Text
queryModelPerformanceFFI (AnalyticsHandle db) = do
  result <- queryModelPerformance db
  return (TL.toStrict (TLE.decodeUtf8 (encode result)))

-- | Query balance consumption (FFI-friendly)
queryBalanceConsumptionFFI :: AnalyticsHandle -> Text -> Text -> IO Text
queryBalanceConsumptionFFI (AnalyticsHandle db) start end = do
  startResult <- parseUTCTime (T.unpack start)
  endResult <- parseUTCTime (T.unpack end)
  case (startResult, endResult) of
    (Left err, _) -> return (T.pack ("Error: " ++ err))
    (_, Left err) -> return (T.pack ("Error: " ++ err))
    (Right start', Right end') -> do
      result <- queryBalanceConsumption db start' end'
      return (TL.toStrict (TLE.decodeUtf8 (encode result)))

-- | Query daily summary
queryDailySummaryFFI :: AnalyticsHandle -> Text -> Text -> IO Text
queryDailySummaryFFI (AnalyticsHandle db) start end = do
  startResult <- parseUTCTime (T.unpack start)
  endResult <- parseUTCTime (T.unpack end)
  case (startResult, endResult) of
    (Left err, _) -> return (T.pack ("Error: " ++ err))
    (_, Left err) -> return (T.pack ("Error: " ++ err))
    (Right start', Right end') -> do
      result <- queryDailySummary db start' end'
      return (TL.toStrict (TLE.decodeUtf8 (encode result)))

-- | Parse UTCTime from ISO string
parseUTCTime :: String -> IO (Either String UTCTime)
parseUTCTime s = do
  let formats = 
        [ "%Y-%m-%dT%H:%M:%S%QZ"
        , "%Y-%m-%dT%H:%M:%SZ"
        , "%Y-%m-%d %H:%M:%S"
        ]
  let parsed = foldl (\acc fmt -> case acc of
        Just _ -> acc
        Nothing -> parseTimeM True defaultTimeLocale fmt s
        ) Nothing formats
  case parsed of
    Just time -> return (Right time)
    Nothing -> return (Left ("Failed to parse timestamp: " ++ s))
