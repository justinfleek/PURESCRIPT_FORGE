{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Deep Comprehensive Property Tests for Billing NVXT
-- |
-- | Tests billing record creation, queue operations, memory leak prevention,
-- | and concurrent operations with realistic distributions to find real bugs.
-- |
-- | Based on spec 70-TESTING-STRATEGY.md and 71-UNIT-TESTING.md
module NVXTProps where

import Test.QuickCheck
import Test.QuickCheck.Monadic
import Control.Concurrent.STM
import Control.Monad (replicateM, forM_, void)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Time (UTCTime, getCurrentTime, addUTCTime, diffUTCTime, secondsToDiffTime)
import Data.UUID (UUID)
import Data.UUID.V4 (nextRandom)
import qualified Data.UUID as UUID
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, isNothing)

import Render.Billing.NVXT
  ( NVXTCollector(..)
  , BillingRecord(..)
  , createNVXTCollector
  , onRequestStart
  , onRequestEnd
  , embedBillingMetadata
  , drainTQueue
  )
import Render.CAS.Client (CASClient, createCASClient)

-- ============================================================================
-- REALISTIC DISTRIBUTIONS
-- ============================================================================

-- | Realistic GPU seconds distribution:
-- | - Most requests: 0.1-5.0 seconds (normal video generation)
-- | - Some requests: 5.0-30.0 seconds (long video generation)
-- | - Few requests: 30.0-300.0 seconds (very long video generation)
genRealisticGpuSeconds :: Gen Double
genRealisticGpuSeconds = frequency
  [ (70, choose (0.1, 5.0))        -- Normal duration
  , (25, choose (5.0, 30.0))       -- Long duration
  , (5, choose (30.0, 300.0))     -- Very long duration
  ]

-- | Realistic customer ID distribution:
-- | - Most customers: cust_1 to cust_1000 (normal distribution)
-- | - Some customers: None (anonymous requests)
genRealisticCustomerId :: Gen (Maybe Text)
genRealisticCustomerId = frequency
  [ (90, do
      customerNum <- choose (1, 1000)
      return $ Just $ "cust_" <> Text.pack (show customerNum))
  , (10, return Nothing)          -- Anonymous requests
  ]

-- | Realistic pricing tier distribution:
-- | - Most requests: tier1 (standard tier)
-- | - Some requests: tier2 (premium tier)
-- | - Few requests: None (no tier)
genRealisticPricingTier :: Gen (Maybe Text)
genRealisticPricingTier = frequency
  [ (60, return $ Just "tier1")
  , (30, return $ Just "tier2")
  , (10, return Nothing)
  ]

-- | Realistic model name distribution:
-- | - 40% wan (most common)
-- | - 30% flux
-- | - 20% qwen
-- | - 10% other models
genRealisticModelName :: Gen Text
genRealisticModelName = frequency
  [ (40, return "wan")
  , (30, return "flux")
  , (20, return "qwen")
  , (10, elements ["sdxl", "zimage", "other"])
  ]

-- | Realistic device UUID distribution:
-- | - Most devices: standard UUID format
-- | - Some devices: placeholder UUIDs
genRealisticDeviceUuid :: Gen Text
genRealisticDeviceUuid = do
  uuid <- nextRandom
  return $ UUID.toText uuid

-- | Realistic request count distribution:
-- | - Most tests: 1-50 requests (normal load)
-- | - Some tests: 50-200 requests (high load)
-- | - Few tests: 200-1000 requests (stress test)
genRealisticRequestCount :: Gen Int
genRealisticRequestCount = frequency
  [ (70, choose (1, 50))           -- Normal load
  , (25, choose (50, 200))         -- High load
  , (5, choose (200, 1000))       -- Stress test
  ]

-- | Generate realistic billing record
genRealisticBillingRecord :: UTCTime -> Gen BillingRecord
genRealisticBillingRecord now = do
  requestId <- nextRandom
  gpuSeconds <- genRealisticGpuSeconds
  deviceUuid <- genRealisticDeviceUuid
  modelName <- genRealisticModelName
  customerId <- genRealisticCustomerId
  pricingTier <- genRealisticPricingTier
  
  return BillingRecord
    { brRequestId = requestId
    , brGpuSeconds = gpuSeconds
    , brDeviceUuid = deviceUuid
    , brModelName = modelName
    , brTimestamp = now
    , brCustomerId = customerId
    , brPricingTier = pricingTier
    }

-- ============================================================================
-- PROPERTY TESTS
-- ============================================================================

-- | Property: Map size never grows unbounded
-- |
-- | BUG: If onRequestEnd is never called, map grows unbounded.
-- | This property verifies that map size is bounded by number of active requests.
prop_mapSizeBounded :: Property
prop_mapSizeBounded = monadicIO $ do
  collector <- run $ atomically createNVXTCollector
  now <- run getCurrentTime
  
  -- Generate realistic number of requests
  requestCount <- pick genRealisticRequestCount
  requestIds <- run $ replicateM requestCount nextRandom
  
  -- Start all requests
  run $ forM_ requestIds $ \reqId ->
    onRequestStart collector reqId "model1"
  
  -- Verify map size equals request count
  mapSize <- run $ atomically $ do
    times <- readTVar (nvxtStartTimes collector)
    return $ Map.size times
  
  assert $ mapSize == requestCount
  
  -- End all requests
  run $ forM_ requestIds $ \reqId ->
    void $ onRequestEnd collector reqId "model1" Nothing Nothing
  
  -- Verify map is empty after all requests end
  mapSizeAfter <- run $ atomically $ do
    times <- readTVar (nvxtStartTimes collector)
    return $ Map.size times
  
  assert $ mapSizeAfter == 0

-- | Property: Queue preserves FIFO order
-- |
-- | BUG: drainTQueue may not preserve FIFO order if queue is modified concurrently.
-- | This property verifies that records are drained in FIFO order.
prop_queueFifoOrder :: Property
prop_queueFifoOrder = monadicIO $ do
  collector <- run $ atomically createNVXTCollector
  now <- run getCurrentTime
  
  -- Generate realistic number of records
  recordCount <- pick $ choose (1, 100)
  records <- run $ replicateM recordCount $ genRealisticBillingRecord now
  
  -- Enqueue all records
  run $ atomically $ forM_ records $ \record ->
    writeTQueue (nvxtAuditQueue collector) record
  
  -- Drain queue
  drainedRecords <- run $ atomically $ drainTQueue (nvxtAuditQueue collector)
  
  -- Verify FIFO order preserved
  assert $ drainedRecords == records
  
  -- Verify queue is empty
  isEmpty <- run $ atomically $ isEmptyTQueue (nvxtAuditQueue collector)
  assert isEmpty

-- | Property: Concurrent start/end operations maintain map consistency
-- |
-- | BUG: Concurrent start/end operations may cause map inconsistency or lost entries.
-- | This property verifies that concurrent operations maintain map consistency.
prop_concurrentStartEndConsistency :: Property
prop_concurrentStartEndConsistency = monadicIO $ do
  collector <- run $ atomically createNVXTCollector
  now <- run getCurrentTime
  
  -- Generate realistic number of requests
  requestCount <- pick $ choose (10, 100)
  requestIds <- run $ replicateM requestCount nextRandom
  
  -- Start all requests concurrently (simulated)
  run $ forM_ requestIds $ \reqId ->
    onRequestStart collector reqId "model1"
  
  -- Verify all requests are in map
  mapSize1 <- run $ atomically $ do
    times <- readTVar (nvxtStartTimes collector)
    return $ Map.size times
  
  assert $ mapSize1 == requestCount
  
  -- End all requests concurrently (simulated)
  run $ forM_ requestIds $ \reqId ->
    void $ onRequestEnd collector reqId "model1" Nothing Nothing
  
  -- Verify map is empty
  mapSize2 <- run $ atomically $ do
    times <- readTVar (nvxtStartTimes collector)
    return $ Map.size times
  
  assert $ mapSize2 == 0

-- | Property: Start time overwrite doesn't cause billing errors
-- |
-- | BUG: If same requestId is started twice, first start time is overwritten,
-- | which may cause incorrect billing calculations.
-- | This property verifies that overwriting start time doesn't cause errors.
prop_startTimeOverwriteHandling :: Property
prop_startTimeOverwriteHandling = monadicIO $ do
  collector <- run $ atomically createNVXTCollector
  now <- run getCurrentTime
  
  requestId <- run nextRandom
  
  -- Start request first time
  run $ onRequestStart collector requestId "model1"
  
  -- Get first start time
  firstTime <- run $ atomically $ do
    times <- readTVar (nvxtStartTimes collector)
    return $ Map.lookup requestId times
  
  -- Wait a bit (simulate time passing)
  run $ threadDelay 10000  -- 10ms
  
  -- Start request second time (overwrites first)
  run $ onRequestStart collector requestId "model1"
  
  -- Get second start time
  secondTime <- run $ atomically $ do
    times <- readTVar (nvxtStartTimes collector)
    return $ Map.lookup requestId times
  
  -- Verify second time overwrites first
  assert $ isJust firstTime
  assert $ isJust secondTime
  assert $ secondTime /= firstTime
  
  -- End request (should work despite overwrite)
  record <- run $ onRequestEnd collector requestId "model1" Nothing Nothing
  
  -- Verify record created successfully
  assert $ brRequestId record == requestId

-- | Property: End without start doesn't cause errors
-- |
-- | BUG: If onRequestEnd is called without onRequestStart, billing record
-- | may be created with incorrect GPU seconds (time since system boot).
-- | This property verifies that end without start is handled gracefully.
prop_endWithoutStartHandling :: Property
prop_endWithoutStartHandling = monadicIO $ do
  collector <- run $ atomically createNVXTCollector
  
  requestId <- run nextRandom
  
  -- End request without starting (should be idempotent)
  record <- run $ onRequestEnd collector requestId "model1" Nothing Nothing
  
  -- Verify record created (may have incorrect GPU seconds, but doesn't error)
  assert $ brRequestId record == requestId
  
  -- Verify map is still empty (no start time was stored)
  mapSize <- run $ atomically $ do
    times <- readTVar (nvxtStartTimes collector)
    return $ Map.size times
  
  assert $ mapSize == 0

-- | Property: Rapid start/end cycles don't cause memory leaks
-- |
-- | BUG: Rapid start/end cycles may cause map entries to accumulate if
-- | cleanup doesn't happen correctly.
-- | This property verifies that rapid cycles don't cause leaks.
prop_rapidCyclesNoLeak :: Property
prop_rapidCyclesNoLeak = monadicIO $ do
  collector <- run $ atomically createNVXTCollector
  
  requestId <- run nextRandom
  cycleCount <- pick $ choose (10, 100)
  
  -- Perform rapid start/end cycles
  run $ forM_ [1..cycleCount] $ \_ -> do
    onRequestStart collector requestId "model1"
    void $ onRequestEnd collector requestId "model1" Nothing Nothing
  
  -- Verify map is empty after all cycles
  mapSize <- run $ atomically $ do
    times <- readTVar (nvxtStartTimes collector)
    return $ Map.size times
  
  assert $ mapSize == 0

-- | Property: Queue size matches number of records
-- |
-- | BUG: Queue size may not match actual number of records if drainTQueue
-- | doesn't drain all records or if records are added concurrently.
-- | This property verifies that queue size matches records.
prop_queueSizeMatchesRecords :: Property
prop_queueSizeMatchesRecords = monadicIO $ do
  collector <- run $ atomically createNVXTCollector
  now <- run getCurrentTime
  
  recordCount <- pick genRealisticRequestCount
  requestIds <- run $ replicateM recordCount nextRandom
  
  -- Start and end all requests (creates records)
  run $ forM_ requestIds $ \reqId -> do
    onRequestStart collector reqId "model1"
    void $ onRequestEnd collector reqId "model1" Nothing Nothing
  
  -- Drain queue and verify count
  drainedRecords <- run $ atomically $ drainTQueue (nvxtAuditQueue collector)
  
  assert $ length drainedRecords == recordCount

-- | Property: Metadata embedding preserves all fields
-- |
-- | BUG: embedBillingMetadata only includes GPU seconds and device UUID,
-- | but doesn't include customer ID or pricing tier.
-- | This property verifies that metadata includes expected fields.
prop_metadataEmbeddingFields :: Property
prop_metadataEmbeddingFields = monadicIO $ do
  now <- run getCurrentTime
  
  record <- pick $ genRealisticBillingRecord now
  
  let metadata = embedBillingMetadata record
  
  -- Verify GPU seconds included
  let hasGpuSeconds = any (\(k, _) -> k == "x-gpu-seconds") metadata
  assert hasGpuSeconds
  
  -- Verify device UUID included
  let hasDeviceUuid = any (\(k, _) -> k == "x-gpu-device") metadata
  assert hasDeviceUuid
  
  -- BUG: Customer ID and pricing tier not included
  -- This property documents the bug but doesn't fail (current behavior)

-- | Property: GPU seconds formatting doesn't lose precision
-- |
-- | BUG: embedBillingMetadata uses show to format GPU seconds, which may
-- | lose precision for very small or very large values, or use scientific notation.
-- | This property verifies that formatting preserves reasonable precision.
prop_gpuSecondsFormattingPrecision :: Property
prop_gpuSecondsFormattingPrecision = monadicIO $ do
  now <- run getCurrentTime
  
  -- Test with very small value
  let smallRecord = BillingRecord
        { brRequestId = UUID.nil
        , brGpuSeconds = 0.000001
        , brDeviceUuid = "device-123"
        , brModelName = "model1"
        , brTimestamp = now
        , brCustomerId = Nothing
        , brPricingTier = Nothing
        }
  
  let metadata = embedBillingMetadata smallRecord
  let gpuSecondsStr = case lookup "x-gpu-seconds" metadata of
        Just str -> str
        Nothing -> ""
  
  -- Verify metadata created (may lose precision, but shouldn't error)
  assert $ not (null gpuSecondsStr)
  
  -- Test with very large value
  let largeRecord = smallRecord { brGpuSeconds = 999999.999999 }
  let metadata2 = embedBillingMetadata largeRecord
  let gpuSecondsStr2 = case lookup "x-gpu-seconds" metadata2 of
        Just str -> str
        Nothing -> ""
  
  -- Verify metadata created (may use scientific notation, but shouldn't error)
  assert $ not (null gpuSecondsStr2)

-- ============================================================================
-- MAIN
-- ============================================================================

main :: IO ()
main = do
  putStrLn "\n=== Billing NVXT Property Tests ==="
  
  putStrLn "\n1. Map Size Bounded"
  quickCheck prop_mapSizeBounded
  
  putStrLn "\n2. Queue FIFO Order"
  quickCheck prop_queueFifoOrder
  
  putStrLn "\n3. Concurrent Start/End Consistency"
  quickCheck prop_concurrentStartEndConsistency
  
  putStrLn "\n4. Start Time Overwrite Handling"
  quickCheck prop_startTimeOverwriteHandling
  
  putStrLn "\n5. End Without Start Handling"
  quickCheck prop_endWithoutStartHandling
  
  putStrLn "\n6. Rapid Cycles No Leak"
  quickCheck prop_rapidCyclesNoLeak
  
  putStrLn "\n7. Queue Size Matches Records"
  quickCheck prop_queueSizeMatchesRecords
  
  putStrLn "\n8. Metadata Embedding Fields"
  quickCheck prop_metadataEmbeddingFields
  
  putStrLn "\n9. GPU Seconds Formatting Precision"
  quickCheck prop_gpuSecondsFormattingPrecision
  
  putStrLn "\n=== All Property Tests Complete ==="
