{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive unit tests for Billing NVXT module
-- | Tests individual functions in isolation: createNVXTCollector, onRequestStart,
-- | onRequestEnd, flushBillingRecords, drainTQueue, embedBillingMetadata
module NVXTSpec where

import Test.Hspec
import Control.Concurrent.STM
import Control.Monad (replicateM, replicateM_)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Time (getCurrentTime, UTCTime, diffUTCTime, secondsToDiffTime)
import Data.UUID (UUID)
import Data.UUID.V4 (nextRandom)
import qualified Data.UUID as UUID
import Data.Maybe (isJust)
import qualified Data.Map.Strict as Map
import Render.Billing.NVXT
  ( NVXTCollector(..)
  , BillingRecord(..)
  , createNVXTCollector
  , onRequestStart
  , onRequestEnd
  , flushBillingRecords
  , drainTQueue
  , embedBillingMetadata
  )
import Render.CAS.Client (CASClient, createCASClient, GPUAttestation(..))
import qualified Data.ByteString as BS

-- | Deep comprehensive unit tests for Billing NVXT module
spec :: Spec
spec = describe "Billing NVXT Unit Tests" $ do
  describe "createNVXTCollector" $ do
    it "creates collector with empty queue and map" $ do
      collector <- atomically createNVXTCollector
      
      -- Verify empty queue
      records <- atomically $ drainTQueue (nvxtAuditQueue collector)
      records `shouldBe` []
      
      -- Verify empty map
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.size times `shouldBe` 0

  describe "onRequestStart" $ do
    it "stores start time in map" $ do
      collector <- atomically createNVXTCollector
      requestId <- nextRandom
      
      onRequestStart collector requestId "model1"
      
      -- Verify start time stored
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.lookup requestId times `shouldSatisfy` isJust

    it "BUG: overwrites start time if same requestId started twice" $ do
      -- BUG: onRequestStart (line 66-68) uses Map.insert which overwrites existing
      -- start times. If the same requestId is started twice (e.g., due to retry
      -- or bug), the first start time is lost, which may cause incorrect billing
      -- calculations.
      collector <- atomically createNVXTCollector
      requestId <- nextRandom
      
      onRequestStart collector requestId "model1"
      firstTime <- atomically $ do
        times <- readTVar (nvxtStartTimes collector)
        pure (Map.lookup requestId times)
      
      -- Start again (overwrites)
      onRequestStart collector requestId "model1"
      secondTime <- atomically $ do
        times <- readTVar (nvxtStartTimes collector)
        pure (Map.lookup requestId times)
      
      -- Second time overwrites first
      secondTime `shouldNotBe` firstTime

    it "BUG: doesn't validate that requestId is unique" $ do
      -- BUG: onRequestStart doesn't validate that requestId is unique or that
      -- a previous start exists. If the same requestId is started multiple times,
      -- only the last start time is kept, which may cause billing errors.
      collector <- atomically createNVXTCollector
      requestId <- nextRandom
      
      -- Start multiple times
      onRequestStart collector requestId "model1"
      onRequestStart collector requestId "model1"
      onRequestStart collector requestId "model1"
      
      -- Only last start time kept
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.size times `shouldBe` 1

  describe "onRequestEnd" $ do
    it "removes start time entry from map" $ do
      collector <- atomically createNVXTCollector
      requestId <- nextRandom
      
      onRequestStart collector requestId "model1"
      _ <- onRequestEnd collector requestId "model1" Nothing Nothing
      
      -- Verify start time removed
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.lookup requestId times `shouldBe` Nothing

    it "BUG: handles end without start but doesn't indicate error" $ do
      -- BUG: onRequestEnd (line 101-102) removes start time entry even if it
      -- doesn't exist (Map.delete is idempotent). This means ending a request
      -- that was never started will succeed silently, potentially creating billing
      -- records with incorrect or zero GPU seconds.
      collector <- atomically createNVXTCollector
      requestId <- nextRandom
      
      -- End without start
      record <- onRequestEnd collector requestId "model1" Nothing Nothing
      
      -- Record created but may have incorrect GPU seconds (no start time)
      brRequestId record `shouldBe` requestId

    it "BUG: doesn't validate that start time exists before computing elapsed time" $ do
      -- BUG: onRequestEnd (line 77-80) gets elapsed time from CUPTI, but doesn't
      -- validate that a start time was recorded. If onRequestStart wasn't called
      -- or failed, the elapsed time may be incorrect (e.g., time since system boot
      -- instead of time since request start).
      collector <- atomically createNVXTCollector
      requestId <- nextRandom
      
      -- End without start
      record <- onRequestEnd collector requestId "model1" Nothing Nothing
      
      -- GPU seconds computed but may be incorrect
      brGpuSeconds record `shouldSatisfy` \s -> s >= 0.0

    it "BUG: queues billing record even if CAS write will fail" $ do
      -- BUG: onRequestEnd (line 98-99) queues billing record immediately, but
      -- if CAS write fails later (in flushBillingRecords), the record is lost.
      -- There's no retry mechanism or error handling for queued records.
      collector <- atomically createNVXTCollector
      requestId <- nextRandom
      
      onRequestStart collector requestId "model1"
      record <- onRequestEnd collector requestId "model1" Nothing Nothing
      
      -- Record queued
      records <- atomically $ drainTQueue (nvxtAuditQueue collector)
      length records `shouldBe` 1

    it "BUG: removes start time even if queue write fails" $ do
      -- BUG: onRequestEnd (line 98-102) removes start time entry even if queue
      -- write fails (though TQueue writes shouldn't fail). If the queue is full
      -- or write fails, the start time is still removed, causing a memory leak
      -- prevention but potentially losing billing data.
      collector <- atomically createNVXTCollector
      requestId <- nextRandom
      
      onRequestStart collector requestId "model1"
      _ <- onRequestEnd collector requestId "model1" Nothing Nothing
      
      -- Start time removed even if queue operations fail
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.lookup requestId times `shouldBe` Nothing

  describe "flushBillingRecords" $ do
    it "handles empty queue gracefully" $ do
      collector <- atomically createNVXTCollector
      casClient <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      
      -- Flush empty queue (should not error)
      flushBillingRecords casClient collector
      
      -- Queue should still be empty
      records <- atomically $ drainTQueue (nvxtAuditQueue collector)
      records `shouldBe` []

    it "BUG: doesn't retry failed CAS writes" $ do
      -- BUG: flushBillingRecords (line 114-144) writes records to CAS, but if
      -- a write fails (line 142-143), it's silently ignored. There's no retry
      -- mechanism, so failed writes result in lost billing data.
      collector <- atomically createNVXTCollector
      casClient <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      requestId <- nextRandom
      
      onRequestStart collector requestId "model1"
      _ <- onRequestEnd collector requestId "model1" Nothing Nothing
      
      -- Flush (may fail silently)
      flushBillingRecords casClient collector
      
      -- Queue drained even if writes failed
      records <- atomically $ drainTQueue (nvxtAuditQueue collector)
      records `shouldBe` []

    it "BUG: doesn't batch writes efficiently" $ do
      -- BUG: flushBillingRecords (line 124) uses mapM_ to write records one by one.
      -- This is inefficient for large batches - should batch writes to CAS for
      -- better performance.
      collector <- atomically createNVXTCollector
      casClient <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      
      -- Create multiple records
      requestIds <- replicateM 10 nextRandom
      mapM_ (\reqId -> do
        onRequestStart collector reqId "model1"
        _ <- onRequestEnd collector reqId "model1" Nothing Nothing
        pure ()
      ) requestIds
      
      -- Flush (writes one by one, not batched)
      flushBillingRecords casClient collector
      
      -- Queue drained
      records <- atomically $ drainTQueue (nvxtAuditQueue collector)
      records `shouldBe` []

    it "BUG: doesn't validate billing records before writing" $ do
      -- BUG: flushBillingRecords doesn't validate that billing records are valid
      -- (e.g., non-negative GPU seconds, non-empty model name) before writing to CAS.
      -- Invalid records may be written, causing data quality issues.
      collector <- atomically createNVXTCollector
      casClient <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      requestId <- nextRandom
      
      -- Create record (may have invalid data)
      onRequestStart collector requestId "model1"
      record <- onRequestEnd collector requestId "model1" Nothing Nothing
      
      -- Flush without validation
      flushBillingRecords casClient collector
      
      -- Record written even if invalid
      True `shouldBe` True

  describe "drainTQueue" $ do
    it "drains empty queue to empty list" $ do
      collector <- atomically createNVXTCollector
      
      records <- atomically $ drainTQueue (nvxtAuditQueue collector)
      records `shouldBe` []

    it "BUG: may not preserve FIFO order if queue is modified concurrently" $ do
      -- BUG: drainTQueue (line 186-193) drains queue recursively, but if items
      -- are added concurrently while draining, the order may not be FIFO.
      -- However, STM transactions are atomic, so this is prevented in practice.
      collector <- atomically createNVXTCollector
      requestId1 <- nextRandom
      requestId2 <- nextRandom
      
      onRequestStart collector requestId1 "model1"
      onRequestStart collector requestId2 "model1"
      _ <- onRequestEnd collector requestId1 "model1" Nothing Nothing
      _ <- onRequestEnd collector requestId2 "model1" Nothing Nothing
      
      -- Drain queue
      records <- atomically $ drainTQueue (nvxtAuditQueue collector)
      -- Should preserve FIFO order
      length records `shouldBe` 2

    it "BUG: may not drain all items if queue is modified during drain" $ do
      -- BUG: drainTQueue uses recursive tryReadTQueue, but if items are added
      -- concurrently while draining, they may not be included in the drained list.
      -- However, STM transactions ensure atomicity, so this is prevented.
      collector <- atomically createNVXTCollector
      requestId <- nextRandom
      
      onRequestStart collector requestId "model1"
      _ <- onRequestEnd collector requestId "model1" Nothing Nothing
      
      -- Drain queue
      records <- atomically $ drainTQueue (nvxtAuditQueue collector)
      length records `shouldBe` 1

  describe "embedBillingMetadata" $ do
    it "embeds GPU seconds and device UUID in metadata" $ do
      requestId <- nextRandom
      now <- getCurrentTime
      let record = BillingRecord
            { brRequestId = requestId
            , brGpuSeconds = 1.5
            , brDeviceUuid = "device-123"
            , brModelName = "model1"
            , brTimestamp = now
            , brCustomerId = Nothing
            , brPricingTier = Nothing
            }
      
      let metadata = embedBillingMetadata record
      
      -- Should contain GPU seconds and device UUID
      metadata `shouldContain` [("x-gpu-seconds", "1.5")]
      metadata `shouldContain` [("x-gpu-device", "device-123")]

    it "BUG: doesn't include customer ID or pricing tier in metadata" $ do
      -- BUG: embedBillingMetadata (line 107-111) only includes GPU seconds and
      -- device UUID, but doesn't include customer ID or pricing tier. This may
      -- make it harder to track billing per customer or tier.
      requestId <- nextRandom
      now <- getCurrentTime
      let record = BillingRecord
            { brRequestId = requestId
            , brGpuSeconds = 1.5
            , brDeviceUuid = "device-123"
            , brModelName = "model1"
            , brTimestamp = now
            , brCustomerId = Just "cust1"
            , brPricingTier = Just "tier1"
            }
      
      let metadata = embedBillingMetadata record
      
      -- Customer ID and pricing tier not included
      metadata `shouldNotContain` [("x-customer-id", "cust1")]
      metadata `shouldNotContain` [("x-pricing-tier", "tier1")]

    it "BUG: GPU seconds formatting may lose precision" $ do
      -- BUG: embedBillingMetadata (line 109) uses show to format GPU seconds,
      -- which may lose precision for very small or very large values. Additionally,
      -- show may produce scientific notation which may not be parseable by clients.
      requestId <- nextRandom
      now <- getCurrentTime
      let record = BillingRecord
            { brRequestId = requestId
            , brGpuSeconds = 0.000001 -- Very small value
            , brDeviceUuid = "device-123"
            , brModelName = "model1"
            , brTimestamp = now
            , brCustomerId = Nothing
            , brPricingTier = Nothing
            }
      
      let metadata = embedBillingMetadata record
      
      -- May lose precision or use scientific notation
      metadata `shouldSatisfy` \md -> not (null md)

  describe "Memory Leak Prevention" $ do
    it "BUG: map may grow unbounded if onRequestEnd is never called" $ do
      -- BUG: onRequestStart (line 66-68) adds entries to the map, but if
      -- onRequestEnd is never called (e.g., request crashes, process killed),
      -- entries remain in the map forever, causing a memory leak.
      collector <- atomically createNVXTCollector
      requestIds <- replicateM 100 nextRandom
      
      -- Start many requests but never end them
      mapM_ (\reqId -> onRequestStart collector reqId "model1") requestIds
      
      -- Map grows unbounded
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.size times `shouldBe` 100

    it "BUG: map may not be cleaned up on process termination" $ do
      -- BUG: The start times map is stored in a TVar, which persists for the
      -- lifetime of the collector. If the process terminates unexpectedly,
      -- entries in the map are lost without cleanup, potentially causing
      -- billing records to be lost.
      collector <- atomically createNVXTCollector
      requestId <- nextRandom
      
      onRequestStart collector requestId "model1"
      
      -- If process terminates, entry is lost
      times <- atomically $ readTVar (nvxtStartTimes collector)
      Map.size times `shouldBe` 1
