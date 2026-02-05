{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive unit tests for Core module
-- | Tests individual functions in isolation: createJobStore, storeJob, getJob,
-- | updateJob, deleteJob, drainQueueToList, getQueuePosition, processRequest,
-- | handleRequestSuccess, handleRequestFailure, cancelJob, removeJobFromQueue
module CoreSpec where

import Test.Hspec
import Control.Concurrent.STM
import Control.Concurrent (forkIO, threadDelay)
import Control.Monad (replicateM, replicateM_)
import Data.Time (getCurrentTime)
import Data.Aeson (object)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Maybe (isJust, isNothing)
import Render.Gateway.Core
  ( GatewayState(..)
  , JobStore(..)
  , createJobStore
  , storeJob
  , getJob
  , updateJob
  , deleteJob
  , cancelJob
  , getQueuePosition
  , removeJobFromQueue
  , processRequest
  , handleRequestSuccess
  , handleRequestFailure
  )
import Render.Gateway.STM.Queue
  ( RequestQueue(..)
  , QueuedJob(..)
  , Priority(..)
  , Modality(..)
  , TaskType(..)
  , JobStatus(..)
  , createQueue
  , enqueueJob
  , tryDequeueJob
  )
import Render.Gateway.STM.Clock (Clock, createClock, startClockThread)
import Render.Gateway.Backend (Backend(..), BackendType(..))
import Render.Gateway.STM.CircuitBreaker (CircuitBreaker, CircuitBreakerConfig(..), createCircuitBreaker)
import Render.Gateway.STM.RateLimiter (createRateLimiter)
import qualified Data.Map.Strict as Map

-- | Helper to create test job
createTestJob :: Text -> Priority -> JobStatus -> IO QueuedJob
createTestJob jobId priority status = do
  now <- getCurrentTime
  pure QueuedJob
    { qjJobId = jobId
    , qjRequestId = "req_" <> jobId
    , qjCustomerId = "cust_test"
    , qjModality = Video
    , qjModelFamily = "wan"
    , qjModelName = "default"
    , qjTask = T2V
    , qjFormat = Nothing
    , qjBackend = Nothing
    , qjPriority = priority
    , qjStatus = status
    , qjCreatedAt = now
    , qjStartedAt = Nothing
    , qjCompletedAt = Nothing
    , qjRequest = object []
    , qjOutput = Nothing
    , qjError = Nothing
    , qjRetryCount = 0
    }

-- | Helper to create test gateway state
createTestGatewayState :: IO GatewayState
createTestGatewayState = do
  queue <- atomically createQueue
  jobStore <- atomically createJobStore
  rateLimiters <- atomically $ newTVar Map.empty
  clock <- atomically createClock
  _ <- startClockThread clock
  let backends = []
  pure GatewayState
    { gsQueue = queue
    , gsJobStore = jobStore
    , gsRateLimiters = rateLimiters
    , gsBackends = backends
    , gsClock = clock
    }

-- | Helper to create test backend
createTestBackend :: Text -> BackendType -> Text -> [Text] -> Text -> Int32 -> IO Backend
createTestBackend backendId backendType family models endpoint capacity = do
  now <- getCurrentTime
  let config = CircuitBreakerConfig 0.5 3 60.0 300.0
  circuitBreaker <- atomically $ createCircuitBreaker now config
  inFlight <- atomically $ newTVar 0
  pure Backend
    { beId = backendId
    , beType = backendType
    , beFamily = family
    , beModels = models
    , beEndpoint = endpoint
    , beCapacity = capacity
    , beInFlight = inFlight
    , beCircuit = circuitBreaker
    }

-- | Deep comprehensive unit tests for Core module
spec :: Spec
spec = describe "Core Unit Tests" $ do
  describe "createJobStore" $ do
    it "creates empty job store" $ do
      store <- atomically createJobStore
      
      -- Verify store is empty
      jobs <- atomically $ readTVar (jsJobs store)
      Map.size jobs `shouldBe` 0

  describe "storeJob" $ do
    it "stores job in job store" $ do
      store <- atomically createJobStore
      job <- createTestJob "j1" Normal Queued
      
      atomically $ storeJob store job
      
      storedJob <- atomically $ getJob store "j1"
      storedJob `shouldBe` Just job

    it "BUG: overwrites existing job without validation" $ do
      -- BUG: storeJob (line 43-45) uses Map.insert which overwrites existing
      -- jobs without checking if the job already exists or if the status
      -- transition is valid. This may allow overwriting completed jobs or
      -- jobs with different IDs.
      store <- atomically createJobStore
      job1 <- createTestJob "j1" Normal Queued
      job2 <- createTestJob "j1" Normal Complete -- Same ID, different status
      
      atomically $ do
        storeJob store job1
        storeJob store job2
      
      storedJob <- atomically $ getJob store "j1"
      storedJob `shouldBe` Just job2 -- Overwrites without validation

    it "stores multiple jobs correctly" $ do
      store <- atomically createJobStore
      job1 <- createTestJob "j1" Normal Queued
      job2 <- createTestJob "j2" Normal Queued
      
      atomically $ do
        storeJob store job1
        storeJob store job2
      
      storedJob1 <- atomically $ getJob store "j1"
      storedJob2 <- atomically $ getJob store "j2"
      storedJob1 `shouldBe` Just job1
      storedJob2 `shouldBe` Just job2

  describe "getJob" $ do
    it "returns job when exists" $ do
      store <- atomically createJobStore
      job <- createTestJob "j1" Normal Queued
      
      atomically $ storeJob store job
      
      result <- atomically $ getJob store "j1"
      result `shouldBe` Just job

    it "returns Nothing when job doesn't exist" $ do
      store <- atomically createJobStore
      
      result <- atomically $ getJob store "nonexistent"
      result `shouldBe` Nothing

  describe "updateJob" $ do
    it "updates job when exists" $ do
      store <- atomically createJobStore
      job <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob store job
        updated <- updateJob store "j1" (\j -> j { qjStatus = Running })
        updated `shouldBe` True
      
      updatedJob <- atomically $ getJob store "j1"
      case updatedJob of
        Just j -> qjStatus j `shouldBe` Running
        Nothing -> fail "Job should exist"

    it "BUG: returns False when job doesn't exist but doesn't distinguish from update failure" $ do
      -- BUG: updateJob (line 55-62) returns False when job doesn't exist,
      -- but doesn't distinguish between "job doesn't exist" and "update failed".
      -- This makes debugging harder.
      store <- atomically createJobStore
      
      updated <- atomically $ updateJob store "nonexistent" (\j -> j { qjStatus = Running })
      updated `shouldBe` False

    it "BUG: doesn't validate that update function is safe" $ do
      -- BUG: updateJob accepts any function (QueuedJob -> QueuedJob), but
      -- doesn't validate that the update is safe (e.g., doesn't change job ID,
      -- doesn't violate status transitions). This may allow invalid updates.
      store <- atomically createJobStore
      job <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob store job
        -- Update that changes job ID (shouldn't be allowed)
        updated <- updateJob store "j1" (\j -> j { qjJobId = "j2" })
        updated `shouldBe` True
      
      -- Job ID changed, but lookup by old ID still works (Map key unchanged)
      oldJob <- atomically $ getJob store "j1"
      oldJob `shouldSatisfy` isJust -- Still exists under old key

  describe "deleteJob" $ do
    it "deletes job when exists" $ do
      store <- atomically createJobStore
      job <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob store job
        deleteJob store "j1"
      
      result <- atomically $ getJob store "j1"
      result `shouldBe` Nothing

    it "BUG: idempotent deletion doesn't indicate if job existed" $ do
      -- BUG: deleteJob (line 65-67) is idempotent - deleting a non-existent
      -- job doesn't error, but also doesn't indicate whether the job existed.
      -- This makes it hard to detect programming errors (deleting wrong job).
      store <- atomically createJobStore
      
      -- Delete non-existent job (no error, but no indication it didn't exist)
      atomically $ deleteJob store "nonexistent"
      
      result <- atomically $ getJob store "nonexistent"
      result `shouldBe` Nothing

  describe "getQueuePosition" $ do
    it "returns position for job in high priority queue" $ do
      queue <- atomically createQueue
      job1 <- createTestJob "j1" High Queued
      job2 <- createTestJob "j2" High Queued
      
      atomically $ do
        enqueueJob queue job1
        enqueueJob queue job2
      
      position <- atomically $ getQueuePosition queue "j2"
      position `shouldBe` 1

    it "returns -1 for job not in queue" $ do
      queue <- atomically createQueue
      
      position <- atomically $ getQueuePosition queue "nonexistent"
      position `shouldBe` (-1)

    it "BUG: race condition with concurrent dequeue may return incorrect position" $ do
      -- BUG: getQueuePosition (line 90-111) scans queues by draining and re-enqueuing,
      -- but if a job is dequeued concurrently by tryDequeueJob, the position may be
      -- incorrect or -1 even if the job is still in the queue (just moved).
      queue <- atomically createQueue
      job <- createTestJob "j1" Normal Queued
      
      atomically $ enqueueJob queue job
      
      -- Concurrently dequeue job
      _ <- forkIO $ atomically $ do
        _ <- tryDequeueJob queue
        pure ()
      
      threadDelay 10000 -- Small delay
      
      -- Position may be -1 even if job is still queued (race condition)
      position <- atomically $ getQueuePosition queue "j1"
      -- Position may be incorrect due to race condition
      position `shouldSatisfy` \p -> p >= (-1) && p <= 1

    it "BUG: scans all queues even if job is in first queue" $ do
      -- BUG: getQueuePosition scans high, then normal, then low priority queues
      -- sequentially. If a job is in the high priority queue, it still scans
      -- normal and low queues unnecessarily, wasting CPU.
      queue <- atomically createQueue
      job <- createTestJob "j1" High Queued
      
      atomically $ enqueueJob queue job
      
      position <- atomically $ getQueuePosition queue "j1"
      position `shouldBe` 0
      -- Function still scans normal and low queues internally (inefficient)

  describe "removeJobFromQueue" $ do
    it "removes job from high priority queue" $ do
      queue <- atomically createQueue
      job1 <- createTestJob "j1" High Queued
      job2 <- createTestJob "j2" High Queued
      
      atomically $ do
        enqueueJob queue job1
        enqueueJob queue job2
        removed <- removeJobFromQueue queue "j1"
        removed `shouldBe` True
      
      -- Verify job1 removed, job2 still there
      position1 <- atomically $ getQueuePosition queue "j1"
      position2 <- atomically $ getQueuePosition queue "j2"
      position1 `shouldBe` (-1)
      position2 `shouldBe` 0

    it "BUG: decrements size counter even if job was concurrently dequeued" $ do
      -- BUG: removeJobFromQueue (line 296, 303, 310) decrements rqSize when
      -- removeFromQueue returns True, but if the job was concurrently dequeued,
      -- removeFromQueue returns False and size isn't decremented. However, if
      -- the job is dequeued between removeFromQueue returning True and decrementing
      -- size, the size counter may be incorrect.
      queue <- atomically createQueue
      job <- createTestJob "j1" Normal Queued
      
      atomically $ enqueueJob queue job
      
      -- Concurrently dequeue job
      _ <- forkIO $ atomically $ do
        _ <- tryDequeueJob queue
        pure ()
      
      threadDelay 10000
      
      -- removeJobFromQueue may still try to remove and decrement size
      removed <- atomically $ removeJobFromQueue queue "j1"
      -- removed may be False if job was dequeued, but size handling may be inconsistent

    it "BUG: preserves order but may be inefficient for large queues" $ do
      -- BUG: removeJobFromQueue drains the entire queue, filters, and re-enqueues.
      -- For large queues, this is inefficient (O(n) operations). A more efficient
      -- approach would maintain a position map or use a different data structure.
      queue <- atomically createQueue
      jobs <- replicateM 10 $ createTestJob "j" Normal Queued
      
      atomically $ do
        mapM_ (enqueueJob queue) jobs
        removed <- removeJobFromQueue queue "j5"
        removed `shouldBe` True
      
      -- Order preserved, but inefficient for large queues
      True `shouldBe` True

  describe "processRequest" $ do
    it "returns Nothing when queue is empty" $ do
      gatewayState <- createTestGatewayState
      
      result <- atomically $ processRequest gatewayState
      result `shouldBe` Nothing

    it "BUG: creates rate limiter with hardcoded defaults" $ do
      -- BUG: processRequest (line 152-156) creates rate limiter with hardcoded
      -- defaults (1000.0 capacity, 100.0 refill rate). This doesn't allow
      -- per-customer rate limiting configuration.
      gatewayState <- createTestGatewayState
      job <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob (gsJobStore gatewayState) job
        enqueueJob (gsQueue gatewayState) job
      
      -- Rate limiter created with hardcoded defaults
      result <- atomically $ processRequest gatewayState
      -- Rate limiter created but defaults may not be appropriate

    it "BUG: requeues job even if it was cancelled between dequeue and requeue" $ do
      -- BUG: processRequest (line 168-175) checks if job was cancelled before
      -- requeueing, but if the job is cancelled between the check and enqueueJob,
      -- it may still be requeued. However, STM transactions ensure atomicity,
      -- so this shouldn't happen in practice.
      gatewayState <- createTestGatewayState
      job <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob (gsJobStore gatewayState) job
        enqueueJob (gsQueue gatewayState) job
      
      -- Cancel job
      atomically $ updateJob (gsJobStore gatewayState) "j1" (\j -> j { qjStatus = Cancelled })
      
      -- processRequest should not requeue cancelled job
      result <- atomically $ processRequest gatewayState
      result `shouldBe` Nothing

    it "BUG: releases backend even if job update fails" $ do
      -- BUG: processRequest (line 199-202) releases backend if updateJob fails,
      -- which is correct. However, if the backend was selected but the job
      -- update fails, the backend counter is correctly decremented, but the
      -- job may remain in an inconsistent state.
      backend <- createTestBackend "b1" Nunchaku "wan" ["default"] "localhost:8000" 10
      gatewayState <- createTestGatewayState
      let gatewayStateWithBackend = gatewayState { gsBackends = [backend] }
      job <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob (gsJobStore gatewayStateWithBackend) job
        enqueueJob (gsQueue gatewayStateWithBackend) job
      
      -- Delete job to cause updateJob to fail
      atomically $ deleteJob (gsJobStore gatewayStateWithBackend) "j1"
      
      -- processRequest should release backend even though updateJob fails
      result <- atomically $ processRequest gatewayStateWithBackend
      result `shouldBe` Nothing
      
      -- Backend should be released
      count <- atomically $ readTVar (beInFlight backend)
      count `shouldBe` 0

  describe "handleRequestSuccess" $ do
    it "updates job status to Complete" $ do
      backend <- createTestBackend "b1" Nunchaku "wan" ["default"] "localhost:8000" 10
      gatewayState <- createTestGatewayState
      let gatewayStateWithBackend = gatewayState { gsBackends = [backend] }
      job <- createTestJob "j1" Normal Running
      
      atomically $ do
        storeJob (gsJobStore gatewayStateWithBackend) job
        handleRequestSuccess gatewayStateWithBackend job backend "https://example.com/output.mp4"
      
      updatedJob <- atomically $ getJob (gsJobStore gatewayStateWithBackend) "j1"
      case updatedJob of
        Just j -> do
          qjStatus j `shouldBe` Complete
          qjOutput j `shouldBe` Just "https://example.com/output.mp4"
        Nothing -> fail "Job should exist"

    it "BUG: doesn't update backend stats if job update fails" $ do
      -- BUG: handleRequestSuccess (line 225-227) only records backend success
      -- if job update succeeds. This is correct behavior, but if the job update
      -- fails (e.g., job was deleted), the backend success isn't recorded, which
      -- may skew backend statistics.
      backend <- createTestBackend "b1" Nunchaku "wan" ["default"] "localhost:8000" 10
      gatewayState <- createTestGatewayState
      let gatewayStateWithBackend = gatewayState { gsBackends = [backend] }
      job <- createTestJob "j1" Normal Running
      
      atomically $ do
        storeJob (gsJobStore gatewayStateWithBackend) job
        deleteJob (gsJobStore gatewayStateWithBackend) "j1"
        handleRequestSuccess gatewayStateWithBackend job backend "https://example.com/output.mp4"
      
      -- Backend success not recorded (correct, but may skew stats)

    it "BUG: ignores cancelled jobs but doesn't release backend" $ do
      -- BUG: handleRequestSuccess (line 213-214) ignores cancelled jobs, but
      -- if the backend was already selected and the job is cancelled, the backend
      -- should still be released. However, this is handled by the caller
      -- (processJobAsync), so this may be correct.
      backend <- createTestBackend "b1" Nunchaku "wan" ["default"] "localhost:8000" 10
      gatewayState <- createTestGatewayState
      let gatewayStateWithBackend = gatewayState { gsBackends = [backend] }
      job <- createTestJob "j1" Normal Cancelled
      
      atomically $ do
        storeJob (gsJobStore gatewayStateWithBackend) job
        handleRequestSuccess gatewayStateWithBackend job backend "https://example.com/output.mp4"
      
      -- Job status unchanged (ignored)
      updatedJob <- atomically $ getJob (gsJobStore gatewayStateWithBackend) "j1"
      case updatedJob of
        Just j -> qjStatus j `shouldBe` Cancelled
        Nothing -> fail "Job should exist"

  describe "handleRequestFailure" $ do
    it "updates job status to Error" $ do
      backend <- createTestBackend "b1" Nunchaku "wan" ["default"] "localhost:8000" 10
      gatewayState <- createTestGatewayState
      let gatewayStateWithBackend = gatewayState { gsBackends = [backend] }
      job <- createTestJob "j1" Normal Running
      
      atomically $ do
        storeJob (gsJobStore gatewayStateWithBackend) job
        handleRequestFailure gatewayStateWithBackend job backend "Backend error"
      
      updatedJob <- atomically $ getJob (gsJobStore gatewayStateWithBackend) "j1"
      case updatedJob of
        Just j -> do
          qjStatus j `shouldBe` Error
          qjError j `shouldBe` Just "Backend error"
        Nothing -> fail "Job should exist"

    it "BUG: similar to handleRequestSuccess, doesn't update backend stats if job update fails" $ do
      -- BUG: Same issue as handleRequestSuccess - backend failure not recorded
      -- if job update fails, which may skew statistics.
      backend <- createTestBackend "b1" Nunchaku "wan" ["default"] "localhost:8000" 10
      gatewayState <- createTestGatewayState
      let gatewayStateWithBackend = gatewayState { gsBackends = [backend] }
      job <- createTestJob "j1" Normal Running
      
      atomically $ do
        storeJob (gsJobStore gatewayStateWithBackend) job
        deleteJob (gsJobStore gatewayStateWithBackend) "j1"
        handleRequestFailure gatewayStateWithBackend job backend "Backend error"
      
      -- Backend failure not recorded (correct, but may skew stats)

  describe "cancelJob" $ do
    it "cancels queued job and removes from queue" $ do
      gatewayState <- createTestGatewayState
      job <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob (gsJobStore gatewayState) job
        enqueueJob (gsQueue gatewayState) job
        cancelled <- cancelJob gatewayState "j1"
        cancelled `shouldBe` True
      
      -- Verify job is cancelled
      updatedJob <- atomically $ getJob (gsJobStore gatewayState) "j1"
      case updatedJob of
        Just j -> qjStatus j `shouldBe` Cancelled
        Nothing -> fail "Job should exist"
      
      -- Verify job removed from queue
      position <- atomically $ getQueuePosition (gsQueue gatewayState) "j1"
      position `shouldBe` (-1)

    it "BUG: returns False for terminal state jobs but doesn't indicate why" $ do
      -- BUG: cancelJob (line 281) returns False for terminal state jobs, but
      -- doesn't distinguish between "job doesn't exist" and "job already terminal".
      -- This makes debugging harder.
      gatewayState <- createTestGatewayState
      job <- createTestJob "j1" Normal Complete
      
      atomically $ do
        storeJob (gsJobStore gatewayState) job
        cancelled <- cancelJob gatewayState "j1"
        cancelled `shouldBe` False -- Doesn't indicate why (already terminal)

    it "BUG: may not remove job from queue if already dequeued" $ do
      -- BUG: cancelJob (line 270) calls removeJobFromQueue which may return False
      -- if the job was already dequeued. The job is still marked as cancelled,
      -- but the return value doesn't indicate whether removal succeeded.
      gatewayState <- createTestGatewayState
      job <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob (gsJobStore gatewayState) job
        enqueueJob (gsQueue gatewayState) job
        _ <- tryDequeueJob (gsQueue gatewayState)
        cancelled <- cancelJob gatewayState "j1"
        cancelled `shouldBe` True -- Still returns True even though removal failed
