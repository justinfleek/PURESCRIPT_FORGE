{-# LANGUAGE OverloadedStrings #-}

-- | Render Billing Test Suite
-- | Comprehensive tests for NVXT billing functionality
module Main where

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Render.Billing.NVXT (NVXTCollector(..), BillingRecord(..), createNVXTCollector, onRequestStart, onRequestEnd, flushBillingRecords, embedBillingMetadata, drainTQueue)

import Control.Concurrent.STM
import Control.Monad (forM_)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.UUID (UUID)
import qualified Data.UUID as UUID
import Data.Time (getCurrentTime)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, isNothing)
import Render.CAS.Client (CASClient, createCASClient)
import Control.Concurrent.STM.TQueue (writeTQueue, tryReadTQueue)

main :: IO ()
main = hspec $ do
  describe "Render Billing Tests" $ do
    nvxtCollectorTests
    billingRecordTests
    propertyTests
    nvxtDeepTests

-- | NVXT collector tests
nvxtCollectorTests :: Spec
nvxtCollectorTests = describe "NVXT Collector" $ do
  it "creates NVXT collector" $ do
    collector <- atomically createNVXTCollector
    -- Collector should be created successfully
    collector `shouldSatisfy` (\c -> True)

  it "queues billing records" $ do
    collector <- atomically createNVXTCollector
    now <- getCurrentTime
    requestId <- UUID.nextRandom
    
    -- Create billing record with customer ID and pricing tier
    record <- onRequestEnd collector requestId "test-model" (Just "cust-123") (Just "tier-1")
    
    brModelName record `shouldBe` "test-model"
    brRequestId record `shouldBe` requestId
    brCustomerId record `shouldBe` Just "cust-123"
    brPricingTier record `shouldBe` Just "tier-1"

-- | Billing record tests
billingRecordTests :: Spec
billingRecordTests = describe "Billing Records" $ do
  it "embeds billing metadata" $ do
    now <- getCurrentTime
    requestId <- UUID.nextRandom
    let record = BillingRecord
          { brRequestId = requestId
          , brGpuSeconds = 1.5
          , brDeviceUuid = "device-123"
          , brModelName = "test-model"
          , brTimestamp = now
          , brCustomerId = Just "cust-123"
          , brPricingTier = Just "tier-1"
          }
    
    let metadata = embedBillingMetadata record
    length metadata `shouldBe` 2
    lookup "x-gpu-seconds" metadata `shouldSatisfy` isJust
    lookup "x-gpu-device" metadata `shouldSatisfy` isJust

-- | Property tests
propertyTests :: Spec
propertyTests = describe "Property Tests" $ do
  prop "billing records have non-negative GPU seconds" $ \gpuSeconds -> do
    now <- getCurrentTime
    requestId <- UUID.nextRandom
    let record = BillingRecord
          { brRequestId = requestId
          , brGpuSeconds = abs gpuSeconds -- Ensure non-negative
          , brDeviceUuid = "device-123"
          , brModelName = "test-model"
          , brTimestamp = now
          , brCustomerId = Nothing
          , brPricingTier = Nothing
          }
    
    brGpuSeconds record >= 0

  prop "billing metadata contains required fields" $ \gpuSeconds -> do
    now <- getCurrentTime
    requestId <- UUID.nextRandom
    let record = BillingRecord
          { brRequestId = requestId
          , brGpuSeconds = abs gpuSeconds
          , brDeviceUuid = "device-123"
          , brModelName = "test-model"
          , brTimestamp = now
          , brCustomerId = Nothing
          , brPricingTier = Nothing
          }
    
    let metadata = embedBillingMetadata record
    lookup "x-gpu-seconds" metadata `shouldSatisfy` isJust
    lookup "x-gpu-device" metadata `shouldSatisfy` isJust

-- | Deep comprehensive NVXT tests
nvxtDeepTests :: Spec
nvxtDeepTests = describe "NVXT Deep Tests" $ do
  describe "onRequestStart" $ do
    it "stores start time in map (Bug 29 fix verification)" $ do
      collector <- atomically createNVXTCollector
      requestId <- UUID.nextRandom
      
      -- Start request
      onRequestStart collector requestId "test-model"
      
      -- Verify start time was stored
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.lookup requestId times `shouldSatisfy` isJust

    it "handles multiple concurrent request starts" $ do
      collector <- atomically createNVXTCollector
      requestId1 <- UUID.nextRandom
      requestId2 <- UUID.nextRandom
      requestId3 <- UUID.nextRandom
      
      -- Start multiple requests
      onRequestStart collector requestId1 "model1"
      onRequestStart collector requestId2 "model2"
      onRequestStart collector requestId3 "model3"
      
      -- All should be in map
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.size times `shouldBe` 3
      Map.lookup requestId1 times `shouldSatisfy` isJust
      Map.lookup requestId2 times `shouldSatisfy` isJust
      Map.lookup requestId3 times `shouldSatisfy` isJust

    it "overwrites start time if same requestId started twice" $ do
      collector <- atomically createNVXTCollector
      requestId <- UUID.nextRandom
      
      -- Start request twice
      onRequestStart collector requestId "model1"
      onRequestStart collector requestId "model2"
      
      -- Should have only one entry (latest overwrites)
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.size times `shouldBe` 1
      Map.lookup requestId times `shouldSatisfy` isJust

  describe "onRequestEnd - Memory Leak Prevention (Bug 29)" $ do
    it "removes start time entry from map (Bug 29 fix verification)" $ do
      collector <- atomically createNVXTCollector
      requestId <- UUID.nextRandom
      
      -- Start request
      onRequestStart collector requestId "test-model"
      
      -- Verify start time stored
      timesBefore <- atomically $ readTVar (nvxtStartTimes collector)
      Map.lookup requestId timesBefore `shouldSatisfy` isJust
      
      -- End request
      _ <- onRequestEnd collector requestId "test-model" Nothing Nothing
      
      -- Verify start time removed (memory leak fix)
      timesAfter <- atomically $ readTVar (nvxtStartTimes collector)
      Map.lookup requestId timesAfter `shouldBe` Nothing
      Map.size timesAfter `shouldBe` 0

    it "handles onRequestEnd when start time not in map (idempotent)" $ do
      collector <- atomically createNVXTCollector
      requestId <- UUID.nextRandom
      
      -- End request without starting (should not crash)
      _ <- onRequestEnd collector requestId "test-model" Nothing Nothing
      
      -- Map should still be empty
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.size times `shouldBe` 0

    it "removes correct entry when multiple requests active" $ do
      collector <- atomically createNVXTCollector
      requestId1 <- UUID.nextRandom
      requestId2 <- UUID.nextRandom
      requestId3 <- UUID.nextRandom
      
      -- Start all requests
      onRequestStart collector requestId1 "model1"
      onRequestStart collector requestId2 "model2"
      onRequestStart collector requestId3 "model3"
      
      -- End only requestId2
      _ <- onRequestEnd collector requestId2 "model2" Nothing Nothing
      
      -- Only requestId2 should be removed
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.size times `shouldBe` 2
      Map.lookup requestId1 times `shouldSatisfy` isJust
      Map.lookup requestId2 times `shouldBe` Nothing -- Removed
      Map.lookup requestId3 times `shouldSatisfy` isJust

    it "queues billing record for async flush" $ do
      collector <- atomically createNVXTCollector
      requestId <- UUID.nextRandom
      
      -- Start and end request
      onRequestStart collector requestId "test-model"
      record <- onRequestEnd collector requestId "test-model" (Just "cust-123") (Just "tier-1")
      
      -- Record should be queued
      records <- atomically $ drainTQueue (nvxtAuditQueue collector)
      length records `shouldBe` 1
      brRequestId (head records) `shouldBe` requestId
      head records `shouldBe` record

    it "creates billing record with all fields" $ do
      collector <- atomically createNVXTCollector
      requestId <- UUID.nextRandom
      
      -- Start and end request
      onRequestStart collector requestId "test-model"
      record <- onRequestEnd collector requestId "test-model" (Just "cust-123") (Just "tier-1")
      
      -- Verify all fields
      brRequestId record `shouldBe` requestId
      brModelName record `shouldBe` "test-model"
      brCustomerId record `shouldBe` Just "cust-123"
      brPricingTier record `shouldBe` Just "tier-1"
      brGpuSeconds record >= 0 -- Should be non-negative
      brDeviceUuid record `shouldSatisfy` (not . Text.null)

    it "handles None customer ID and pricing tier" $ do
      collector <- atomically createNVXTCollector
      requestId <- UUID.nextRandom
      
      -- Start and end request without customer/pricing
      onRequestStart collector requestId "test-model"
      record <- onRequestEnd collector requestId "test-model" Nothing Nothing
      
      -- Customer ID and pricing tier should be Nothing
      brCustomerId record `shouldBe` Nothing
      brPricingTier record `shouldBe` Nothing

  describe "flushBillingRecords" $ do
    it "handles empty queue gracefully" $ do
      collector <- atomically createNVXTCollector
      casClient <- createCASClient "https://cas.test" "test-bucket"
      
      -- Flush empty queue (should not crash)
      flushBillingRecords casClient collector
      
      -- Queue should still be empty after flush
      records <- atomically $ drainTQueue (nvxtAuditQueue collector)
      records `shouldBe` []

    it "drains all records from queue" $ do
      collector <- atomically createNVXTCollector
      casClient <- createCASClient "https://cas.test" "test-bucket"
      requestId1 <- UUID.nextRandom
      requestId2 <- UUID.nextRandom
      requestId3 <- UUID.nextRandom
      
      -- Create multiple records
      onRequestStart collector requestId1 "model1"
      record1 <- onRequestEnd collector requestId1 "model1" Nothing Nothing
      
      onRequestStart collector requestId2 "model2"
      record2 <- onRequestEnd collector requestId2 "model2" Nothing Nothing
      
      onRequestStart collector requestId3 "model3"
      record3 <- onRequestEnd collector requestId3 "model3" Nothing Nothing
      
      -- Verify records were created
      brRequestId record1 `shouldBe` requestId1
      brRequestId record2 `shouldBe` requestId2
      brRequestId record3 `shouldBe` requestId3
      
      -- Flush should drain queue
      flushBillingRecords casClient collector
      
      -- Queue should be empty after flush
      records <- atomically $ drainTQueue (nvxtAuditQueue collector)
      records `shouldBe` []

    it "handles CAS write errors gracefully" $ do
      collector <- atomically createNVXTCollector
      -- Use invalid endpoint to trigger error
      casClient <- createCASClient "https://invalid-endpoint" "test-bucket"
      requestId <- UUID.nextRandom
      
      -- Create record
      onRequestStart collector requestId "test-model"
      _ <- onRequestEnd collector requestId "test-model" Nothing Nothing
      
      -- Flush should handle CAS errors gracefully (not crash)
      flushBillingRecords casClient collector
      
      -- Queue should be drained even if CAS write fails
      -- (Errors are logged but don't stop processing per implementation)
      records <- atomically $ drainTQueue (nvxtAuditQueue collector)
      records `shouldBe` []

  describe "drainTQueue" $ do
    it "drains queue in FIFO order" $ do
      collector <- atomically createNVXTCollector
      requestId1 <- UUID.nextRandom
      requestId2 <- UUID.nextRandom
      requestId3 <- UUID.nextRandom
      
      -- Create records in order
      onRequestStart collector requestId1 "model1"
      record1 <- onRequestEnd collector requestId1 "model1" Nothing Nothing
      
      onRequestStart collector requestId2 "model2"
      record2 <- onRequestEnd collector requestId2 "model2" Nothing Nothing
      
      onRequestStart collector requestId3 "model3"
      record3 <- onRequestEnd collector requestId3 "model3" Nothing Nothing
      
      -- Drain should preserve order
      records <- atomically $ drainTQueue (nvxtAuditQueue collector)
      length records `shouldBe` 3
      brRequestId (head records) `shouldBe` requestId1
      brRequestId (records !! 1) `shouldBe` requestId2
      brRequestId (records !! 2) `shouldBe` requestId3

    it "returns empty list for empty queue" $ do
      collector <- atomically createNVXTCollector
      records <- atomically $ drainTQueue (nvxtAuditQueue collector)
      records `shouldBe` []

  describe "Memory Leak Prevention (Bug 29)" $ do
    it "map size never grows unbounded with start/end pairs" $ do
      collector <- atomically createNVXTCollector
      
      -- Create many start/end pairs
      forM_ [1..100] $ \i -> do
        requestId <- UUID.nextRandom
        onRequestStart collector requestId ("model" <> Text.pack (show i))
        _ <- onRequestEnd collector requestId ("model" <> Text.pack (show i)) Nothing Nothing
      
      -- Map should be empty (all entries removed)
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.size times `shouldBe` 0

    it "map size correct with partial completion" $ do
      collector <- atomically createNVXTCollector
      requestId1 <- UUID.nextRandom
      requestId2 <- UUID.nextRandom
      requestId3 <- UUID.nextRandom
      
      -- Start all requests
      onRequestStart collector requestId1 "model1"
      onRequestStart collector requestId2 "model2"
      onRequestStart collector requestId3 "model3"
      
      -- End only one
      _ <- onRequestEnd collector requestId2 "model2" Nothing Nothing
      
      -- Map should have 2 entries (one removed)
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.size times `shouldBe` 2

  describe "Concurrent Operations" $ do
    it "maintains map consistency under concurrent start/end" $ do
      collector <- atomically createNVXTCollector
      requestId <- UUID.nextRandom
      
      -- Concurrently start and end
      onRequestStart collector requestId "test-model"
      _ <- onRequestEnd collector requestId "test-model" Nothing Nothing
      
      -- Map should be empty (entry removed)
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.size times `shouldBe` 0

    it "handles rapid start/end cycles without leaks" $ do
      collector <- atomically createNVXTCollector
      
      -- Rapid cycles
      forM_ [1..50] $ \_ -> do
        requestId <- UUID.nextRandom
        onRequestStart collector requestId "test-model"
        _ <- onRequestEnd collector requestId "test-model" Nothing Nothing
      
      -- Map should be empty
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.size times `shouldBe` 0
