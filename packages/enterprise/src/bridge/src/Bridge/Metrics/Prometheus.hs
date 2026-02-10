{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

-- | Bridge Metrics Prometheus
-- |
-- | Prometheus-compatible metrics registry with support for
-- | counters, gauges, and histograms. Exports metrics in
-- | the Prometheus text exposition format.
-- |
-- | Dependencies:
-- | - Control.Concurrent.STM: Thread-safe metric storage
-- | - Data.Map: Metric name to value mapping
-- | - Data.Int: Int64 for counter precision
module Bridge.Metrics.Prometheus where

import Control.Concurrent.STM
  ( TVar
  , STM
  , newTVarIO
  , readTVar
  , writeTVar
  , readTVarIO
  , atomically
  )
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Int (Int64)
import Data.Text (Text)
import qualified Data.Text as T

-- | Metric value types
data MetricValue
  = CounterValue Int64
  | GaugeValue Double
  | HistogramValue [Double] -- observed values
  deriving (Eq, Show)

-- | Metric entry: (metric name, help text, value)
type MetricEntry = (Text, Text, MetricValue)

-- | Metric registry (thread-safe map of metric names to entries)
type MetricRegistry = TVar (Map Text MetricEntry)

-- | Create a new empty metric registry
createRegistry :: IO MetricRegistry
createRegistry = newTVarIO Map.empty

-- | Increment a counter metric
-- |
-- | If the counter does not exist, creates it with value 1.
-- | If it exists as a counter, increments by 1.
incrementCounter :: MetricRegistry -> Text -> Text -> IO ()
incrementCounter registry name helpText = atomically $ do
  metrics <- readTVar registry
  let newValue = case Map.lookup name metrics of
        Just (_, _, CounterValue n) -> CounterValue (n + 1)
        _ -> CounterValue 1
  writeTVar registry (Map.insert name (name, helpText, newValue) metrics)

-- | Set a gauge metric to a specific value
-- |
-- | If the gauge does not exist, creates it.
-- | Overwrites any existing value.
setGauge :: MetricRegistry -> Text -> Text -> Double -> IO ()
setGauge registry name helpText value = atomically $ do
  metrics <- readTVar registry
  writeTVar registry (Map.insert name (name, helpText, GaugeValue value) metrics)

-- | Record an observation in a histogram
-- |
-- | If the histogram does not exist, creates it with the single observation.
-- | Appends to existing observations.
observeHistogram :: MetricRegistry -> Text -> Text -> Double -> IO ()
observeHistogram registry name helpText value = atomically $ do
  metrics <- readTVar registry
  let newValue = case Map.lookup name metrics of
        Just (_, _, HistogramValue obs) -> HistogramValue (obs ++ [value])
        _ -> HistogramValue [value]
  writeTVar registry (Map.insert name (name, helpText, newValue) metrics)

-- | Export all metrics in Prometheus text exposition format
-- |
-- | Format:
-- |   # HELP <name> <help>
-- |   # TYPE <name> <type>
-- |   <name> <value>
exportMetrics :: MetricRegistry -> IO Text
exportMetrics registry = do
  metrics <- readTVarIO registry
  let entries = Map.elems metrics
  pure (T.intercalate "\n" (concatMap formatEntry entries) <> "\n")

-- | Format a single metric entry in Prometheus text format
formatEntry :: MetricEntry -> [Text]
formatEntry (name, helpText, value) =
  case value of
    CounterValue n ->
      [ "# HELP " <> name <> " " <> helpText
      , "# TYPE " <> name <> " counter"
      , name <> " " <> T.pack (show n)
      ]
    GaugeValue v ->
      [ "# HELP " <> name <> " " <> helpText
      , "# TYPE " <> name <> " gauge"
      , name <> " " <> T.pack (show v)
      ]
    HistogramValue observations ->
      let count = length observations
          total = sum observations
          buckets = computeBuckets observations defaultBucketBoundaries
      in [ "# HELP " <> name <> " " <> helpText
         , "# TYPE " <> name <> " histogram"
         ]
         ++ map (\(bound, cnt) ->
              name <> "_bucket{le=\"" <> formatBound bound <> "\"} " <> T.pack (show cnt)
            ) buckets
         ++ [ name <> "_bucket{le=\"+Inf\"} " <> T.pack (show count)
            , name <> "_sum " <> T.pack (show total)
            , name <> "_count " <> T.pack (show count)
            ]

-- | Default histogram bucket boundaries
defaultBucketBoundaries :: [Double]
defaultBucketBoundaries = [0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0]

-- | Compute histogram bucket counts
-- |
-- | For each boundary, counts observations less than or equal to the boundary.
-- | Buckets are cumulative per Prometheus convention.
computeBuckets :: [Double] -> [Double] -> [(Double, Int)]
computeBuckets observations boundaries =
  map (\bound -> (bound, length (filter (<= bound) observations))) boundaries

-- | Format a bucket boundary for Prometheus output
formatBound :: Double -> Text
formatBound v = T.pack (show v)
