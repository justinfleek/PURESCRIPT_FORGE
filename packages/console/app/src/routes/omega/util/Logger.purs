-- | Omega API Logger
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/logger.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Omega.Util.Logger
  ( LogLevel(..)
  , MetricValue(..)
  , MetricEntry
  , LogEntry
  , formatMetric
  , formatLog
  , shouldLog
  ) where

import Prelude

import Data.Array (uncons)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

-- | Log level
data LogLevel
  = Debug
  | Info
  | Warn
  | Error

derive instance eqLogLevel :: Eq LogLevel
derive instance ordLogLevel :: Ord LogLevel

instance showLogLevel :: Show LogLevel where
  show Debug = "debug"
  show Info = "info"
  show Warn = "warn"
  show Error = "error"

-- | Metric entry value
data MetricValue
  = MetricString String
  | MetricInt Int
  | MetricNumber Number
  | MetricBool Boolean

instance showMetricValue :: Show MetricValue where
  show (MetricString s) = "\"" <> s <> "\""
  show (MetricInt i) = show i
  show (MetricNumber n) = show n
  show (MetricBool b) = if b then "true" else "false"

-- | Metric entry (key-value pairs for structured logging)
type MetricEntry = Map String MetricValue

-- | Log entry
type LogEntry =
  { level :: LogLevel
  , message :: String
  , timestamp :: String
  }

-- | Format metric as JSON string for logging
-- | Output: _metric:{"key":"value",...}
formatMetric :: MetricEntry -> String
formatMetric entry =
  "_metric:" <> toJson entry

-- | Convert metric entry to JSON
toJson :: MetricEntry -> String
toJson entry =
  "{" <> joinWithComma (map formatPair (Map.toUnfoldable entry)) <> "}"
  where
    formatPair :: Tuple String MetricValue -> String
    formatPair (Tuple key value) = "\"" <> key <> "\":" <> show value
    
    joinWithComma :: Array String -> String
    joinWithComma arr = case uncons arr of
      Nothing -> ""
      Just { head: x, tail: [] } -> x
      Just { head: x, tail: xs } -> x <> "," <> joinWithComma xs

-- | Format log entry
formatLog :: LogEntry -> String
formatLog entry =
  "[" <> entry.timestamp <> "] [" <> show entry.level <> "] " <> entry.message

-- | Check if log level should be logged based on environment
-- | In production, only log info and above
shouldLog :: { isProduction :: Boolean } -> LogLevel -> Boolean
shouldLog { isProduction } level =
  if isProduction
    then level >= Info
    else true

-- | Build metric entry from common request fields
buildRequestMetric ::
  { isStream :: Boolean
  , session :: String
  , request :: String
  , client :: String
  } -> MetricEntry
buildRequestMetric { isStream, session, request, client } =
  Map.fromFoldable
    [ Tuple "is_stream" (MetricBool isStream)
    , Tuple "session" (MetricString session)
    , Tuple "request" (MetricString request)
    , Tuple "client" (MetricString client)
    ]

-- | Add model info to metric
addModelMetric :: String -> MetricEntry -> MetricEntry
addModelMetric model entry =
  Map.insert "model" (MetricString model) entry

-- | Add provider info to metric
addProviderMetric :: String -> MetricEntry -> MetricEntry
addProviderMetric provider entry =
  Map.insert "provider" (MetricString provider) entry

-- | Add API key info to metric
addApiKeyMetric :: String -> String -> MetricEntry -> MetricEntry
addApiKeyMetric apiKey workspaceId entry =
  Map.insert "api_key" (MetricString apiKey) $
  Map.insert "workspace" (MetricString workspaceId) entry

-- | Add token counts to metric
addTokenMetrics ::
  { inputTokens :: Int
  , outputTokens :: Int
  , reasoningTokens :: Maybe Int
  , cacheReadTokens :: Maybe Int
  , cacheWrite5mTokens :: Maybe Int
  , cacheWrite1hTokens :: Maybe Int
  } -> MetricEntry -> MetricEntry
addTokenMetrics tokens entry =
  Map.insert "tokens.input" (MetricInt tokens.inputTokens) $
  Map.insert "tokens.output" (MetricInt tokens.outputTokens) $
  insertMaybe "tokens.reasoning" tokens.reasoningTokens $
  insertMaybe "tokens.cache_read" tokens.cacheReadTokens $
  insertMaybe "tokens.cache_write_5m" tokens.cacheWrite5mTokens $
  insertMaybe "tokens.cache_write_1h" tokens.cacheWrite1hTokens entry
  where
    insertMaybe :: String -> Maybe Int -> MetricEntry -> MetricEntry
    insertMaybe key (Just value) e = Map.insert key (MetricInt value) e
    insertMaybe _ Nothing e = e

-- | Add cost info to metric
addCostMetrics ::
  { inputCost :: Int
  , outputCost :: Int
  , reasoningCost :: Maybe Int
  , cacheReadCost :: Maybe Int
  , cacheWrite5mCost :: Maybe Int
  , cacheWrite1hCost :: Maybe Int
  , totalCost :: Int
  } -> MetricEntry -> MetricEntry
addCostMetrics costs entry =
  Map.insert "cost.input" (MetricInt costs.inputCost) $
  Map.insert "cost.output" (MetricInt costs.outputCost) $
  Map.insert "cost.total" (MetricInt costs.totalCost) $
  insertMaybe "cost.reasoning" costs.reasoningCost $
  insertMaybe "cost.cache_read" costs.cacheReadCost $
  insertMaybe "cost.cache_write_5m" costs.cacheWrite5mCost $
  insertMaybe "cost.cache_write_1h" costs.cacheWrite1hCost entry
  where
    insertMaybe :: String -> Maybe Int -> MetricEntry -> MetricEntry
    insertMaybe key (Just value) e = Map.insert key (MetricInt value) e
    insertMaybe _ Nothing e = e

-- | Add error info to metric
addErrorMetric :: String -> String -> MetricEntry -> MetricEntry
addErrorMetric errorType errorMessage entry =
  Map.insert "error.type" (MetricString errorType) $
  Map.insert "error.message" (MetricString errorMessage) entry

-- | Add timing info to metric
addTimingMetrics ::
  { timeToFirstByte :: Maybe Int
  , timestampFirstByte :: Maybe Int
  , timestampLastByte :: Maybe Int
  , responseLength :: Maybe Int
  } -> MetricEntry -> MetricEntry
addTimingMetrics timing entry =
  insertMaybe "time_to_first_byte" timing.timeToFirstByte $
  insertMaybe "timestamp.first_byte" timing.timestampFirstByte $
  insertMaybe "timestamp.last_byte" timing.timestampLastByte $
  insertMaybe "response_length" timing.responseLength entry
  where
    insertMaybe :: String -> Maybe Int -> MetricEntry -> MetricEntry
    insertMaybe key (Just value) e = Map.insert key (MetricInt value) e
    insertMaybe _ Nothing e = e
