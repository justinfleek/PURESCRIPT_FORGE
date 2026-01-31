{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Render Gateway ClickHouse Client
-- | Hot-path metrics insertion and querying
module Render.ClickHouse.Client where

import Prelude hiding (head, tail)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Time (UTCTime)
import Data.Time.Format (formatTime, defaultTimeLocale)

-- | ClickHouse client handle
data ClickHouseClient = ClickHouseClient
  { chcHost :: Text
  , chcPort :: Int
  , chcDatabase :: Text
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
  }

-- | Insert inference event
insertInferenceEvent :: ClickHouseClient -> InferenceEvent -> IO (Either String ())
insertInferenceEvent client event = do
  -- Build INSERT statement
  let sql = buildInsertStatement event
  
  -- Execute via HTTP interface
  executeQuery client sql

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

-- | Execute query
executeQuery :: ClickHouseClient -> Text -> IO (Either String ())
executeQuery ClickHouseClient {..} sql = do
  -- HTTP POST to ClickHouse
  -- Implementation via http-client
  let url = "http://" <> chcHost <> ":" <> Text.pack (show chcPort) <> "/?database=" <> chcDatabase
  executeHttpPost url sql

-- | Execute HTTP POST request
executeHttpPost :: Text -> Text -> IO (Either String ())
executeHttpPost url body = do
  -- TODO: Implement with http-client
  -- For now, return success
  pure (Right ())

-- | Helper functions
quote :: Text -> Text
quote t = "'" <> escapeQuotes t <> "'"

escapeQuotes :: Text -> Text
escapeQuotes = Text.replace "'" "''"

formatTimestamp :: UTCTime -> Text
formatTimestamp = Text.pack . formatTime defaultTimeLocale "%Y-%m-%d %H:%M:%S.%q"

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
