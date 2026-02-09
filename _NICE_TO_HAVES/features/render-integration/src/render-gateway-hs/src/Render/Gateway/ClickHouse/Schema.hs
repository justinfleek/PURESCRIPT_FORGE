{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Render Gateway ClickHouse Schema
-- | Hot-path metrics storage schema per render_specs.pdf
module Render.Gateway.ClickHouse.Schema where

import Prelude hiding (head, tail)
import Data.Text (Text)

-- | Inference event (raw table)
inferenceEventsTable :: Text
inferenceEventsTable = 
  "CREATE TABLE inference_events (\n\
  \  event_id UUID,\n\
  \  timestamp DateTime64(6, 'UTC'),\n\
  \  customer_id LowCardinality(String),\n\
  \  model_name LowCardinality(String),\n\
  \  model_type Enum8('llm' = 1, 'rectified_flow' = 2, 'other' = 3),\n\
  \  request_id UUID,\n\
  \  input_tokens UInt32,\n\
  \  output_tokens UInt32,\n\
  \  input_dims Array(UInt32),\n\
  \  num_steps UInt16,\n\
  \  queue_time_us UInt64,\n\
  \  inference_time_us UInt64,\n\
  \  total_time_us UInt64,\n\
  \  gpu_seconds Float64,\n\
  \  device_uuid LowCardinality(String),\n\
  \  batch_size UInt16,\n\
  \  status Enum8('success' = 1, 'error' = 2, 'timeout' = 3),\n\
  \  error_code Nullable(String)\n\
  \) ENGINE = MergeTree()\n\
  \PARTITION BY toYYYYMMDD(timestamp)\n\
  \ORDER BY (customer_id, model_name, timestamp)\n\
  \TTL timestamp + INTERVAL 7 DAY TO VOLUME 'cold',\n\
  \    timestamp + INTERVAL 90 DAY DELETE\n\
  \SETTINGS index_granularity = 8192"

-- | Metrics rollup (1-minute materialized view)
metrics1mView :: Text
metrics1mView =
  "CREATE MATERIALIZED VIEW metrics_1m\n\
  \ENGINE = SummingMergeTree()\n\
  \PARTITION BY toYYYYMMDD(window_start)\n\
  \ORDER BY (customer_id, model_name, window_start)\n\
  \AS SELECT\n\
  \  customer_id,\n\
  \  model_name,\n\
  \  model_type,\n\
  \  toStartOfMinute(timestamp) AS window_start,\n\
  \  count() AS request_count,\n\
  \  countIf(status = 'success') AS success_count,\n\
  \  countIf(status = 'error') AS error_count,\n\
  \  sum(total_time_us) AS total_latency_us,\n\
  \  sum(total_time_us * total_time_us) AS total_latency_sq,\n\
  \  min(total_time_us) AS min_latency_us,\n\
  \  max(total_time_us) AS max_latency_us,\n\
  \  sum(input_tokens) AS total_input_tokens,\n\
  \  sum(output_tokens) AS total_output_tokens,\n\
  \  sum(gpu_seconds) AS total_gpu_seconds,\n\
  \  sum(queue_time_us) AS total_queue_time_us,\n\
  \  max(queue_time_us) AS max_queue_time_us\n\
  \FROM inference_events\n\
  \GROUP BY customer_id, model_name, model_type, window_start"

-- | Operator metrics (1-hour materialized view)
operatorMetrics1hView :: Text
operatorMetrics1hView =
  "CREATE MATERIALIZED VIEW operator_metrics_1h\n\
  \ENGINE = SummingMergeTree()\n\
  \PARTITION BY toYYYYMM(window_start)\n\
  \ORDER BY (device_uuid, model_name, window_start)\n\
  \AS SELECT\n\
  \  device_uuid,\n\
  \  model_name,\n\
  \  toStartOfHour(timestamp) AS window_start,\n\
  \  sum(gpu_seconds) AS gpu_seconds_consumed,\n\
  \  count() AS total_requests,\n\
  \  uniqExact(customer_id) AS unique_customers,\n\
  \  max(batch_size) AS max_batch_observed,\n\
  \  avg(batch_size) AS avg_batch_size,\n\
  \  countIf(status = 'error') AS errors,\n\
  \  countIf(status = 'timeout') AS timeouts\n\
  \FROM inference_events\n\
  \GROUP BY device_uuid, model_name, window_start"

-- | Latency quantiles (1-minute materialized view with t-digest)
latencyQuantiles1mView :: Text
latencyQuantiles1mView =
  "CREATE MATERIALIZED VIEW latency_quantiles_1m\n\
  \ENGINE = AggregatingMergeTree()\n\
  \PARTITION BY toYYYYMMDD(window_start)\n\
  \ORDER BY (customer_id, model_name, window_start)\n\
  \AS SELECT\n\
  \  customer_id,\n\
  \  model_name,\n\
  \  toStartOfMinute(timestamp) AS window_start,\n\
  \  quantilesTDigestState(0.5, 0.9, 0.95, 0.99)(total_time_us) AS latency_tdigest\n\
  \FROM inference_events\n\
  \GROUP BY customer_id, model_name, window_start"
