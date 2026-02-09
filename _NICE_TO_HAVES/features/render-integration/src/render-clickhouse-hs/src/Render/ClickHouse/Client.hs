{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Render Gateway ClickHouse Client
-- | Hot-path metrics insertion and querying per render_specs.pdf
module Render.ClickHouse.Client where

import Prelude hiding (head, tail)
import Control.Exception (try, SomeException)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as BSL
import Data.Time (UTCTime)
import Data.Time.Format (formatTime, defaultTimeLocale)
import Network.HTTP.Client (Manager, newManager, defaultManagerSettings, httpLbs, parseRequest, RequestBody(..), responseBody, responseStatus)
import qualified Network.HTTP.Client as HTTP
import Network.HTTP.Types.Status (statusCode)
import Data.Aeson (ToJSON(..), FromJSON(..), encode, decode, object, (.=), Value(..))
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Key (fromText)
import GHC.Generics (Generic)

-- | ClickHouse client handle
data ClickHouseClient = ClickHouseClient
  { chcHost :: Text
  , chcPort :: Int
  , chcDatabase :: Text
  , chcManager :: Manager
  }

-- | Create a ClickHouse client
createClickHouseClient :: Text -> Int -> Text -> IO ClickHouseClient
createClickHouseClient host port database = do
  manager <- newManager defaultManagerSettings
  pure ClickHouseClient
    { chcHost = host
    , chcPort = port
    , chcDatabase = database
    , chcManager = manager
    }

-- | Inference event record
data InferenceEvent = InferenceEvent
  { ieEventId :: Text
  , ieTimestamp :: UTCTime
  , ieCustomerId :: Text
  , ieModelName :: Text
  , ieModelType :: Text -- "llm" | "rectified_flow" | "other"
  , ieRequestId :: Text
  , ieInputTokens :: Maybe Int
  , ieOutputTokens :: Maybe Int
  , ieInputDims :: Maybe [Int]
  , ieNumSteps :: Maybe Int
  , ieQueueTimeUs :: Int
  , ieInferenceTimeUs :: Int
  , ieTotalTimeUs :: Int
  , ieGpuSeconds :: Double
  , ieDeviceUuid :: Text
  , ieBatchSize :: Int
  , ieStatus :: Text -- "success" | "error" | "timeout"
  , ieErrorCode :: Maybe Text
  } deriving (Show, Eq, Generic)

instance ToJSON InferenceEvent
instance FromJSON InferenceEvent

-- | Metrics aggregate for reconciliation
data MetricsAggregate = MetricsAggregate
  { maCustomerId :: Text
  , maModelName :: Text
  , maRequestCount :: Int
  , maGpuSeconds :: Double
  , maStartTime :: UTCTime
  , maEndTime :: UTCTime
  } deriving (Show, Eq, Generic)

instance ToJSON MetricsAggregate
instance FromJSON MetricsAggregate

-- | Insert inference event
insertInferenceEvent :: ClickHouseClient -> InferenceEvent -> IO (Either String ())
insertInferenceEvent client event = do
  -- Build INSERT statement
  let sql = buildInsertStatement event

  -- Execute via HTTP interface
  executeQuery client sql

-- | Insert batch of inference events (more efficient)
insertInferenceEventBatch :: ClickHouseClient -> [InferenceEvent] -> IO (Either String ())
insertInferenceEventBatch client events = do
  if null events
    then pure (Right ())
    else do
      let sql = "INSERT INTO inference_events FORMAT JSONEachRow\n" <>
                Text.decodeUtf8 (BSL.toStrict (encode events))
      executeQuery client sql

-- | Query metrics aggregates for a time range
queryMetricsAggregates :: ClickHouseClient -> UTCTime -> UTCTime -> IO (Either String [MetricsAggregate])
queryMetricsAggregates client startTime endTime = do
  let sql = Text.unlines
        [ "SELECT"
        , "  customer_id,"
        , "  model_name,"
        , "  count() AS request_count,"
        , "  sum(gpu_seconds) AS gpu_seconds,"
        , "  min(timestamp) AS start_time,"
        , "  max(timestamp) AS end_time"
        , "FROM inference_events"
        , "WHERE timestamp >= " <> formatTimestamp startTime
        , "  AND timestamp < " <> formatTimestamp endTime
        , "  AND status = 'success'"
        , "GROUP BY customer_id, model_name"
        , "FORMAT JSONEachRow"
        ]

  result <- executeQueryWithResponse client sql
  case result of
    Left err -> pure (Left err)
    Right body ->
      case decodeMetricsAggregates body of
        Nothing -> pure (Left "Failed to decode metrics aggregates")
        Just aggs -> pure (Right aggs)

-- | Query total GPU seconds for a customer in a time range
queryCustomerGpuSeconds :: ClickHouseClient -> Text -> UTCTime -> UTCTime -> IO (Either String Double)
queryCustomerGpuSeconds client customerId startTime endTime = do
  let sql = Text.unlines
        [ "SELECT sum(gpu_seconds) AS total_gpu_seconds"
        , "FROM inference_events"
        , "WHERE customer_id = " <> quote customerId
        , "  AND timestamp >= " <> formatTimestamp startTime
        , "  AND timestamp < " <> formatTimestamp endTime
        , "  AND status = 'success'"
        , "FORMAT JSONEachRow"
        ]

  result <- executeQueryWithResponse client sql
  case result of
    Left err -> pure (Left err)
    Right body ->
      -- JSONEachRow format returns one JSON object per line
      -- Parse first line (should be only one result from SUM query)
      let lines' = filter (not . Text.null) $ Text.lines (Text.decodeUtf8 body)
      in case lines' of
        [] -> pure (Right 0.0)  -- No results means 0 GPU seconds
        (firstLine:_) ->
          case decode (BSL.fromStrict (Text.encodeUtf8 firstLine)) of
            Nothing -> pure (Right 0.0)  -- Failed to decode, return 0
            Just (obj :: Aeson.Object) ->
              case KM.lookup (fromText "total_gpu_seconds") obj of
                Just (Aeson.Number n) -> pure (Right (realToFrac n :: Double))
                _ -> pure (Right 0.0)  -- Missing field or wrong type, return 0

-- | Build INSERT statement
buildInsertStatement :: InferenceEvent -> Text
buildInsertStatement InferenceEvent {..} =
  "INSERT INTO inference_events VALUES (" <>
  quote ieEventId <> ", " <>
  formatTimestamp ieTimestamp <> ", " <>
  quote ieCustomerId <> ", " <>
  quote ieModelName <> ", " <>
  quote ieModelType <> ", " <>
  quote ieRequestId <> ", " <>
  formatMaybeInt ieInputTokens <> ", " <>
  formatMaybeInt ieOutputTokens <> ", " <>
  formatMaybeArray ieInputDims <> ", " <>
  formatMaybeInt ieNumSteps <> ", " <>
  showText ieQueueTimeUs <> ", " <>
  showText ieInferenceTimeUs <> ", " <>
  showText ieTotalTimeUs <> ", " <>
  showText ieGpuSeconds <> ", " <>
  quote ieDeviceUuid <> ", " <>
  showText ieBatchSize <> ", " <>
  quote ieStatus <> ", " <>
  formatMaybeText ieErrorCode <>
  ")"

-- | Execute query (no result expected)
executeQuery :: ClickHouseClient -> Text -> IO (Either String ())
executeQuery client sql = do
  result <- executeQueryWithResponse client sql
  case result of
    Left err -> pure (Left err)
    Right _ -> pure (Right ())

-- | Execute query and return response body
executeQueryWithResponse :: ClickHouseClient -> Text -> IO (Either String ByteString)
executeQueryWithResponse ClickHouseClient {..} sql = do
  result <- try $ do
    let url = Text.unpack $ "http://" <> chcHost <> ":" <> Text.pack (show chcPort) <> "/?database=" <> chcDatabase

    initialRequest <- parseRequest url
    let request = initialRequest
          { HTTP.method = "POST"
          , HTTP.requestBody = RequestBodyBS (Text.encodeUtf8 sql)
          , HTTP.requestHeaders =
              [ ("Content-Type", "text/plain; charset=utf-8")
              ]
          }

    response <- httpLbs request chcManager

    case statusCode (responseStatus response) of
      200 -> pure (Right (BSL.toStrict (responseBody response)))
      code -> pure (Left $ "ClickHouse query failed with status " <> show code <>
                          ": " <> show (BSL.toStrict (responseBody response)))

  case result of
    Left (e :: SomeException) -> pure (Left $ "ClickHouse query error: " <> show e)
    Right r -> pure r

-- | Decode metrics aggregates from JSON lines (exported for testing)
decodeMetricsAggregates :: ByteString -> Maybe [MetricsAggregate]
decodeMetricsAggregates body =
  let lines' = filter (not . Text.null) $ Text.lines (Text.decodeUtf8 body)
  in sequence $ map (decode . BSL.fromStrict . Text.encodeUtf8) lines'

-- | Helper functions
quote :: Text -> Text
quote t = "'" <> escapeQuotes t <> "'"

escapeQuotes :: Text -> Text
escapeQuotes = Text.replace "'" "''"

formatTimestamp :: UTCTime -> Text
formatTimestamp = Text.pack . formatTime defaultTimeLocale "'%Y-%m-%d %H:%M:%S'"

formatMaybeInt :: Maybe Int -> Text
formatMaybeInt Nothing = "NULL"
formatMaybeInt (Just n) = showText n

formatMaybeArray :: Maybe [Int] -> Text
formatMaybeArray Nothing = "[]"
formatMaybeArray (Just xs) = "[" <> Text.intercalate "," (map showText xs) <> "]"

formatMaybeText :: Maybe Text -> Text
formatMaybeText Nothing = "NULL"
formatMaybeText (Just t) = quote t

showText :: Show a => a -> Text
showText = Text.pack . show

-- | Health check - verify ClickHouse connection
healthCheck :: ClickHouseClient -> IO (Either String ())
healthCheck client = do
  result <- executeQueryWithResponse client "SELECT 1"
  case result of
    Left err -> pure (Left err)
    Right _ -> pure (Right ())
