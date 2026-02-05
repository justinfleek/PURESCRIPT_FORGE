{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

-- | Prometheus Metrics - Metrics Export for Monitoring
-- |
-- | **What:** Exports Prometheus-compatible metrics for monitoring and alerting.
-- |         Tracks request counts, latencies, error rates, and business metrics.
-- | **Why:** Enables production monitoring, alerting, and performance analysis.
-- |         Standard Prometheus format ensures compatibility with monitoring stacks.
-- | **How:** Maintains counters, gauges, and histograms using STM. Exposes metrics
-- |         via HTTP endpoint in Prometheus text format.
-- |
-- | **Dependencies:**
-- | - `Control.Concurrent.STM`: Thread-safe metrics storage
-- | - `Data.Text`: Text handling
-- |
-- | **Mathematical Foundation:**
-- | - **Counter:** Monotonically increasing value (e.g., total requests)
-- | - **Gauge:** Value that can go up or down (e.g., active connections)
-- | - **Histogram:** Distribution of values (e.g., request latency)
-- |
-- | **Usage Example:**
-- | ```haskell
-- | import Bridge.Metrics.Prometheus as Metrics
-- |
-- | -- Increment counter
-- | Metrics.incrementCounter Metrics.requestsTotal ["method=\"GET\""]
-- |
-- | -- Record latency
-- | Metrics.observeHistogram Metrics.requestLatency ["method=\"GET\""] 0.123
-- | ```
module Bridge.Metrics.Prometheus where

module Bridge.Metrics.Prometheus where

import Prelude hiding (read, sum)
import Control.Concurrent.STM
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import Data.Int (Int64)
import Data.List (intercalate, sum)

-- | Metric value
data MetricValue
  = CounterValue Int64
  | GaugeValue Double
  | HistogramValue [Double] -- Bucket values

-- | Metric entry
type MetricEntry = (T.Text, T.Text, T.Text, MetricValue) -- (name, help, labels, value)

-- | Metrics registry (STM-based)
type MetricRegistry = TVar (Map.Map T.Text MetricEntry)

-- | Create metric registry
createRegistry :: IO MetricRegistry
createRegistry = newTVarIO Map.empty

-- | Increment counter
-- |
-- | **Purpose:** Increments a counter metric.
-- | **Parameters:**
-- | - `registry`: Metric registry
-- | - `name`: Metric name (e.g., "bridge_requests_total")
-- | - `help`: Metric help text
-- | - `labels`: Label string (e.g., "method=\"GET\"")
incrementCounter :: MetricRegistry -> T.Text -> T.Text -> T.Text -> IO ()
incrementCounter registry name help labels = do
  atomically $ do
    metrics <- readTVar registry
    let key = name <> "{" <> labels <> "}"
    case Map.lookup key metrics of
      Just (n, h, l, CounterValue v) -> do
        writeTVar registry (Map.insert key (n, h, l, CounterValue (v + 1)) metrics)
      _ -> do
        writeTVar registry (Map.insert key (name, help, labels, CounterValue 1) metrics)

-- | Set gauge value
-- |
-- | **Purpose:** Sets a gauge metric value.
-- | **Parameters:**
-- | - `registry`: Metric registry
-- | - `name`: Metric name
-- | - `help`: Metric help text
-- | - `labels`: Label string
-- | - `value`: Gauge value
setGauge :: MetricRegistry -> T.Text -> T.Text -> T.Text -> Double -> IO ()
setGauge registry name help labels value = do
  atomically $ do
    metrics <- readTVar registry
    let key = name <> "{" <> labels <> "}"
    writeTVar registry (Map.insert key (name, help, labels, GaugeValue value) metrics)

-- | Observe histogram value
-- |
-- | **Purpose:** Records a value in a histogram metric (simplified - uses single bucket).
-- | **Parameters:**
-- | - `registry`: Metric registry
-- | - `name`: Metric name
-- | - `help`: Metric help text
-- | - `labels`: Label string
-- | - `value`: Observed value
observeHistogram :: MetricRegistry -> T.Text -> T.Text -> T.Text -> Double -> IO ()
observeHistogram registry name help labels value = do
  atomically $ do
    metrics <- readTVar registry
    let key = name <> "{" <> labels <> "}"
    case Map.lookup key metrics of
      Just (n, h, l, HistogramValue buckets) -> do
        writeTVar registry (Map.insert key (n, h, l, HistogramValue (buckets ++ [value])) metrics)
      _ -> do
        writeTVar registry (Map.insert key (name, help, labels, HistogramValue [value]) metrics)

-- | Export metrics in Prometheus text format
-- |
-- | **Purpose:** Exports all metrics in Prometheus text format for scraping.
-- | **Parameters:**
-- | - `registry`: Metric registry
-- | **Returns:** Prometheus text format string
exportMetrics :: MetricRegistry -> IO T.Text
exportMetrics registry = do
  metrics <- atomically (readTVar registry)
  let lines = Map.foldMapWithKey formatMetric metrics
  pure (T.unlines lines)
  where
    formatMetric :: T.Text -> MetricEntry -> [T.Text]
    formatMetric key (name, help, labels, value) = do
      let helpLine = "# HELP " <> name <> " " <> help
      let typeLine = case value of
            CounterValue _ -> "# TYPE " <> name <> " counter"
            GaugeValue _ -> "# TYPE " <> name <> " gauge"
            HistogramValue _ -> "# TYPE " <> name <> " histogram"
      let valueLine = case value of
            CounterValue v -> name <> "{" <> labels <> "} " <> T.pack (show v)
            GaugeValue v -> name <> "{" <> labels <> "} " <> T.pack (show v)
            HistogramValue buckets -> do
              let count = length buckets
              let sum = sum buckets
              name <> "{" <> labels <> ",le=\"+Inf\"} " <> T.pack (show count) <> "\n" <>
              name <> "_sum{" <> labels <> "} " <> T.pack (show sum) <> "\n" <>
              name <> "_count{" <> labels <> "} " <> T.pack (show count)
      [helpLine, typeLine, valueLine]
