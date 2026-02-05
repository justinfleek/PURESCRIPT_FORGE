{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive tests for ClickHouse Schema module
-- | Tests schema definitions, SQL correctness, and bug detection
module SchemaSpec where

import Test.Hspec
import Data.Text (Text)
import qualified Data.Text as Text
import Render.Gateway.ClickHouse.Schema
  ( inferenceEventsTable
  , metrics1mView
  , operatorMetrics1hView
  , latencyQuantiles1mView
  )

-- | Deep comprehensive tests for ClickHouse Schema module
spec :: Spec
spec = describe "ClickHouse Schema Deep Tests" $ do
  describe "inferenceEventsTable" $ do
    it "defines inference_events table schema" $ do
      let schema = inferenceEventsTable
      -- Schema should contain table name
      Text.isInfixOf "inference_events" schema `shouldBe` True
      -- BUG: Schema may not be correctly defined
      -- This test documents the need for schema validation

    it "includes all required fields" $ do
      let schema = inferenceEventsTable
      -- Schema should include all required fields
      Text.isInfixOf "event_id" schema `shouldBe` True
      Text.isInfixOf "timestamp" schema `shouldBe` True
      Text.isInfixOf "customer_id" schema `shouldBe` True
      Text.isInfixOf "model_name" schema `shouldBe` True
      Text.isInfixOf "gpu_seconds" schema `shouldBe` True
      -- BUG: Schema may be missing required fields
      -- This test documents the potential issue

    it "includes correct data types" $ do
      let schema = inferenceEventsTable
      -- Schema should use correct data types
      Text.isInfixOf "UUID" schema `shouldBe` True
      Text.isInfixOf "DateTime64" schema `shouldBe` True
      Text.isInfixOf "LowCardinality" schema `shouldBe` True
      -- BUG: Schema may use incorrect data types
      -- This test documents the potential issue

    it "includes correct indexes" $ do
      let schema = inferenceEventsTable
      -- Schema should include ORDER BY clause
      Text.isInfixOf "ORDER BY" schema `shouldBe` True
      -- BUG: Schema may have incorrect indexes
      -- This test documents the potential issue

    it "includes TTL configuration" $ do
      let schema = inferenceEventsTable
      -- Schema should include TTL configuration
      Text.isInfixOf "TTL" schema `shouldBe` True
      -- BUG: TTL configuration may be incorrect
      -- This test documents the potential issue

  describe "metrics1mView" $ do
    it "defines metrics_1m materialized view" $ do
      let view = metrics1mView
      -- View should contain view name
      Text.isInfixOf "metrics_1m" view `shouldBe` True
      -- BUG: View may not be correctly defined
      -- This test documents the need for view validation

    it "includes aggregation functions" $ do
      let view = metrics1mView
      -- View should include aggregation functions
      Text.isInfixOf "count()" view `shouldBe` True
      Text.isInfixOf "sum(" view `shouldBe` True
      -- BUG: View may be missing aggregation functions
      -- This test documents the potential issue

    it "includes correct grouping" $ do
      let view = metrics1mView
      -- View should include GROUP BY clause
      Text.isInfixOf "GROUP BY" view `shouldBe` True
      -- BUG: Grouping may be incorrect
      -- This test documents the potential issue

  describe "operatorMetrics1hView" $ do
    it "defines operator_metrics_1h materialized view" $ do
      let view = operatorMetrics1hView
      -- View should contain view name
      Text.isInfixOf "operator_metrics_1h" view `shouldBe` True
      -- BUG: View may not be correctly defined
      -- This test documents the need for view validation

    it "includes device-level aggregations" $ do
      let view = operatorMetrics1hView
      -- View should include device-level aggregations
      Text.isInfixOf "device_uuid" view `shouldBe` True
      -- BUG: View may be missing device-level aggregations
      -- This test documents the potential issue

  describe "latencyQuantiles1mView" $ do
    it "defines latency_quantiles_1m materialized view" $ do
      let view = latencyQuantiles1mView
      -- View should contain view name
      Text.isInfixOf "latency_quantiles_1m" view `shouldBe` True
      -- BUG: View may not be correctly defined
      -- This test documents the need for view validation

    it "includes quantile calculations" $ do
      let view = latencyQuantiles1mView
      -- View should include quantile calculations
      Text.isInfixOf "quantilesTDigestState" view `shouldBe` True
      -- BUG: Quantile calculations may be incorrect
      -- This test documents the potential issue

  describe "SQL Correctness" $ do
    it "produces valid SQL syntax" $ do
      -- BUG: inferenceEventsTable (line 12-38) is a static SQL string.
      -- If there are syntax errors (missing commas, typos, invalid keywords),
      -- ClickHouse will reject the schema at creation time, but the error
      -- may not be caught until deployment.
      let schema = inferenceEventsTable
      
      -- Basic syntax checks:
      -- 1. Should start with CREATE TABLE
      Text.isPrefixOf "CREATE TABLE" schema `shouldBe` True
      
      -- 2. Should have opening and closing parentheses for table definition
      let openParens = Text.length (Text.filter (== '(') schema)
      let closeParens = Text.length (Text.filter (== ')') schema)
      openParens > 0 `shouldBe` True
      closeParens > 0 `shouldBe` True
      
      -- 3. Should have ENGINE clause
      Text.isInfixOf "ENGINE" schema `shouldBe` True
      
      -- BUG: Static SQL strings don't have compile-time validation.
      -- If there's a typo (e.g., "CREATE TABEL" instead of "CREATE TABLE"),
      -- it won't be caught until runtime when ClickHouse tries to execute it.
      -- Solution: Use a SQL parser or validation library to check syntax.
      
      -- Test all schemas/views
      let view1 = metrics1mView
      let view2 = operatorMetrics1hView
      let view3 = latencyQuantiles1mView
      
      -- All should start with CREATE
      Text.isPrefixOf "CREATE" view1 `shouldBe` True
      Text.isPrefixOf "CREATE" view2 `shouldBe` True
      Text.isPrefixOf "CREATE" view3 `shouldBe` True

    it "has balanced parentheses" $ do
      let schema = inferenceEventsTable
      let openParens = Text.length (Text.filter (== '(') schema)
      let closeParens = Text.length (Text.filter (== ')') schema)
      -- Parentheses should be balanced
      openParens `shouldBe` closeParens
      -- BUG: Schema may have unbalanced parentheses
      -- This test documents the potential issue

    it "has balanced quotes" $ do
      let schema = inferenceEventsTable
      let singleQuotes = Text.length (Text.filter (== '\'') schema)
      -- Single quotes should be even (balanced)
      (singleQuotes `mod` 2) `shouldBe` 0
      -- BUG: Schema may have unbalanced quotes
      -- This test documents the potential issue

  describe "Bug Detection" $ do
    it "BUG: schema may have SQL injection vulnerabilities" $ do
      -- BUG: inferenceEventsTable (line 12-38) is a static string, so SQL injection
      -- is not possible from user input. However, if the schema is ever constructed
      -- dynamically (e.g., from configuration), SQL injection could occur.
      -- Additionally, if field names or values are interpolated, injection is possible.
      let schema = inferenceEventsTable
      
      -- BUG: Check for potential injection patterns if schema were dynamic:
      -- 1. Single quotes that could be escaped
      -- 2. Semicolons that could terminate statements
      -- 3. Comments (-- or /*) that could hide malicious code
      
      -- Since schema is static, these checks verify it doesn't contain dangerous patterns
      -- that could be exploited if schema construction becomes dynamic.
      let hasSemicolon = Text.isInfixOf ";" schema
      -- BUG: Semicolons in CREATE TABLE are normal (statement terminator),
      -- but if schema were constructed dynamically, multiple semicolons could allow
      -- multiple statement execution.
      hasSemicolon `shouldBe` True  -- Expected in valid SQL
      
      -- BUG: If schema construction becomes dynamic (e.g., from config file),
      -- user-controlled input must be properly escaped/quoted to prevent injection.
      -- Solution: Always use parameterized queries or proper escaping for dynamic SQL.

    it "BUG: schema may not match actual table structure" $ do
      -- BUG: inferenceEventsTable (line 12-38) defines the schema, but if the actual
      -- ClickHouse table is created manually or modified, it may not match.
      -- This causes issues when:
      -- 1. Code expects fields that don't exist
      -- 2. Code inserts data with wrong types
      -- 3. Views reference fields that don't exist
      let schema = inferenceEventsTable
      let view1 = metrics1mView
      
      -- BUG: metrics1mView (line 41-65) references fields from inference_events:
      -- - customer_id, model_name, model_type, timestamp, status, total_time_us,
      --   input_tokens, output_tokens, gpu_seconds, queue_time_us
      -- If inferenceEventsTable doesn't define these fields correctly, view will fail.
      
      -- Verify view references exist in table schema
      Text.isInfixOf "customer_id" schema `shouldBe` True
      Text.isInfixOf "model_name" schema `shouldBe` True
      Text.isInfixOf "model_type" schema `shouldBe` True
      Text.isInfixOf "timestamp" schema `shouldBe` True
      Text.isInfixOf "status" schema `shouldBe` True
      Text.isInfixOf "total_time_us" schema `shouldBe` True
      Text.isInfixOf "input_tokens" schema `shouldBe` True
      Text.isInfixOf "output_tokens" schema `shouldBe` True
      Text.isInfixOf "gpu_seconds" schema `shouldBe` True
      Text.isInfixOf "queue_time_us" schema `shouldBe` True
      
      -- BUG: If schema is modified but views aren't updated, views will fail at creation.
      -- Solution: Use schema migration tools or validation to ensure consistency.

    it "BUG: schema may have incorrect data types" $ do
      -- BUG: inferenceEventsTable (line 12-38) uses specific ClickHouse data types.
      -- If types are incorrect, it can cause:
      -- 1. Data insertion failures (wrong type)
      -- 2. Performance issues (wrong type for use case)
      -- 3. Storage inefficiency (overly large types)
      -- 4. Precision loss (wrong numeric type)
      let schema = inferenceEventsTable
      
      -- BUG: Check for common type issues:
      -- 1. event_id should be UUID (not String) for performance
      Text.isInfixOf "event_id UUID" schema `shouldBe` True
      
      -- 2. timestamp should be DateTime64(6, 'UTC') for microsecond precision
      Text.isInfixOf "DateTime64" schema `shouldBe` True
      
      -- 3. customer_id and model_name should be LowCardinality(String) for compression
      Text.isInfixOf "customer_id LowCardinality" schema `shouldBe` True
      Text.isInfixOf "model_name LowCardinality" schema `shouldBe` True
      
      -- 4. gpu_seconds should be Float64 (not Int) for fractional values
      Text.isInfixOf "gpu_seconds Float64" schema `shouldBe` True
      
      -- BUG: If types are wrong:
      -- - UUID fields as String: slower lookups, more storage
      -- - DateTime instead of DateTime64: loss of microsecond precision
      -- - String instead of LowCardinality(String): less compression
      -- - Int instead of Float64: can't store fractional GPU seconds
      
      -- BUG: Check view types match expected usage
      let view1 = metrics1mView
      -- View should use SummingMergeTree for aggregations
      Text.isInfixOf "SummingMergeTree" view1 `shouldBe` True

    it "BUG: schema may have incorrect indexes" $ do
      -- BUG: inferenceEventsTable (line 12-38) uses ORDER BY for primary key/index.
      -- If ORDER BY is incorrect, it can cause:
      -- 1. Slow queries (wrong index order)
      -- 2. Poor partition pruning
      -- 3. Inefficient range scans
      let schema = inferenceEventsTable
      
      -- BUG: ORDER BY should match common query patterns:
      -- - Queries often filter by customer_id, then model_name, then timestamp
      -- - ORDER BY (customer_id, model_name, timestamp) matches this pattern
      Text.isInfixOf "ORDER BY" schema `shouldBe` True
      Text.isInfixOf "customer_id" schema `shouldBe` True
      Text.isInfixOf "model_name" schema `shouldBe` True
      Text.isInfixOf "timestamp" schema `shouldBe` True
      
      -- BUG: If ORDER BY order is wrong (e.g., timestamp first), queries filtering
      -- by customer_id will be slow (can't use index efficiently).
      -- Solution: ORDER BY should match query filter order (most selective first).
      
      -- BUG: PARTITION BY should match TTL and query patterns
      -- PARTITION BY toYYYYMMDD(timestamp) allows efficient partition pruning
      -- for date-range queries and TTL operations.
      Text.isInfixOf "PARTITION BY" schema `shouldBe` True
      Text.isInfixOf "toYYYYMMDD" schema `shouldBe` True
      
      -- BUG: If PARTITION BY is wrong, TTL operations may be inefficient
      -- (scanning all partitions instead of specific date partitions).

    it "BUG: schema may have incorrect TTL configuration" $ do
      -- BUG: inferenceEventsTable (line 36-37) defines TTL:
      -- - 7 days: move to 'cold' volume
      -- - 90 days: delete
      -- If TTL is incorrect, it can cause:
      -- 1. Data retention too short (data deleted too early)
      -- 2. Data retention too long (storage costs)
      -- 3. Cold volume not configured (TTL fails)
      let schema = inferenceEventsTable
      
      -- BUG: TTL configuration should be present
      Text.isInfixOf "TTL" schema `shouldBe` True
      
      -- BUG: TTL should reference timestamp field
      Text.isInfixOf "timestamp + INTERVAL" schema `shouldBe` True
      
      -- BUG: Check TTL intervals are reasonable:
      -- - 7 days to cold: reasonable for hot/cold storage tiering
      -- - 90 days delete: reasonable for compliance/retention
      -- If intervals are wrong (e.g., 1 day delete), data may be lost prematurely.
      Text.isInfixOf "7 DAY" schema `shouldBe` True
      Text.isInfixOf "90 DAY" schema `shouldBe` True
      
      -- BUG: TTL references 'cold' volume - if volume doesn't exist, TTL will fail.
      -- Solution: Ensure 'cold' volume is configured in ClickHouse.
      
      -- BUG: TTL uses INTERVAL syntax - if syntax is wrong, TTL won't work.
      -- Check for proper INTERVAL syntax
      Text.isInfixOf "INTERVAL" schema `shouldBe` True
      
      -- BUG: If TTL configuration is missing or incorrect, data may:
      -- - Never be moved to cold storage (high costs)
      -- - Never be deleted (unbounded growth)
      -- - Be deleted too early (data loss)
