{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive integration tests for Gateway ↔ Job Store interaction
-- | Tests job creation, updates, retrieval, and deletion
module GatewayJobStoreSpec where

import Test.Hspec
import Control.Concurrent.STM
import Data.Text (Text)
import Data.Time (getCurrentTime, UTCTime)
import Data.Aeson (object)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, isNothing)

import Render.Gateway.STM.Queue
import Render.Gateway.STM.RateLimiter
import Render.Gateway.STM.CircuitBreaker
import Render.Gateway.STM.Clock
import Render.Gateway.Core
import Render.Gateway.Backend
import qualified Data.Text as Text

-- | Helper to create test job
createJob :: UTCTime -> Text -> Priority -> QueuedJob
createJob now jobId priority = QueuedJob
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
  , qjStatus = Queued
  , qjCreatedAt = now
  , qjStartedAt = Nothing
  , qjCompletedAt = Nothing
  , qjRequest = object []
  , qjOutput = Nothing
  , qjError = Nothing
  , qjRetryCount = 0
  }

-- | Deep comprehensive integration tests for Gateway ↔ Job Store
spec :: Spec
spec = describe "Gateway ↔ Job Store Integration Deep Tests" $ do
  describe "Job Creation" $ do
    it "stores job and retrieves it correctly" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j1" Normal
      atomically $ storeJob store job
      
      retrieved <- atomically $ getJob store "j1"
      case retrieved of
        Just j -> do
          qjJobId j `shouldBe` "j1"
          qjStatus j `shouldBe` Queued
        Nothing -> expectationFailure "Job should exist"

    it "overwrites existing job with same ID" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job1 = createJob now "j1" Normal
      let job2 = createJob now "j1" High  -- Same ID, different priority
      
      atomically $ do
        storeJob store job1
        storeJob store job2
      
      retrieved <- atomically $ getJob store "j1"
      case retrieved of
        Just j -> qjPriority j `shouldBe` High  -- Should be overwritten
        Nothing -> expectationFailure "Job should exist"

    it "stores multiple jobs independently" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job1 = createJob now "j1" Normal
      let job2 = createJob now "j2" High
      let job3 = createJob now "j3" Low
      
      atomically $ do
        storeJob store job1
        storeJob store job2
        storeJob store job3
      
      retrieved1 <- atomically $ getJob store "j1"
      retrieved2 <- atomically $ getJob store "j2"
      retrieved3 <- atomically $ getJob store "j3"
      
      retrieved1 `shouldSatisfy` isJust
      retrieved2 `shouldSatisfy` isJust
      retrieved3 `shouldSatisfy` isJust

  describe "Job Updates" $ do
    it "updates job status correctly" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j1" Normal
      atomically $ storeJob store job
      
      -- Update status to Running
      updated <- atomically $ updateJob store "j1" (\j -> j { qjStatus = Running })
      updated `shouldBe` True
      
      retrieved <- atomically $ getJob store "j1"
      case retrieved of
        Just j -> qjStatus j `shouldBe` Running
        Nothing -> expectationFailure "Job should exist"

    it "updates job fields correctly" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j1" Normal
      atomically $ storeJob store job
      
      -- Update multiple fields
      updated <- atomically $ updateJob store "j1" (\j -> j
        { qjStatus = Complete
        , qjOutput = Just "https://cdn.example.com/output.mp4"
        , qjCompletedAt = Just now
        })
      updated `shouldBe` True
      
      retrieved <- atomically $ getJob store "j1"
      case retrieved of
        Just j -> do
          qjStatus j `shouldBe` Complete
          qjOutput j `shouldSatisfy` isJust
          qjCompletedAt j `shouldSatisfy` isJust
        Nothing -> expectationFailure "Job should exist"

    it "returns False when updating non-existent job" $ do
      store <- atomically createJobStore
      
      updated <- atomically $ updateJob store "nonexistent" (\j -> j { qjStatus = Running })
      updated `shouldBe` False

    it "preserves unrelated fields during update" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j1" Normal
      atomically $ storeJob store job
      
      -- Update only status
      updated <- atomically $ updateJob store "j1" (\j -> j { qjStatus = Running })
      updated `shouldBe` True
      
      retrieved <- atomically $ getJob store "j1"
      case retrieved of
        Just j -> do
          qjJobId j `shouldBe` "j1"
          qjCustomerId j `shouldBe` "cust_test"
          qjPriority j `shouldBe` Normal  -- Unchanged
        Nothing -> expectationFailure "Job should exist"

    it "BUG: updateJob may have race condition with concurrent delete" $ do
      -- BUG: If job is deleted between lookup and adjust,
      -- updateJob may fail silently or cause inconsistent state
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j1" Normal
      atomically $ storeJob store job
      
      -- BUG: Race condition - if deleteJob and updateJob are called concurrently,
      -- STM serializes them, but the order matters. If delete happens first, update
      -- will return False (job doesn't exist). If update happens first, delete will
      -- remove the updated job. This is correct STM behavior, but documents the
      -- potential for lost updates if operations are not coordinated.
      
      -- Test concurrent delete and update in same transaction
      updated <- atomically $ do
        storeJob store job
        deleteJob store "j1"
        updateJob store "j1" (\j -> j { qjStatus = Running })
      -- BUG: updateJob returns False because job was deleted first
      updated `shouldBe` False
      
      -- Verify job was deleted (not updated)
      retrieved <- atomically $ getJob store "j1"
      retrieved `shouldBe` Nothing
      
      -- BUG: If updateJob and deleteJob are called in separate transactions,
      -- STM serializes them, but the final state depends on order:
      -- - If update happens first: job is updated, then deleted
      -- - If delete happens first: update returns False, job is deleted
      -- This is correct STM behavior, but documents potential for lost updates
      
      -- Test reverse order (update then delete)
      let job2 = createJob now "j2" Normal
      atomically $ do
        storeJob store job2
        updated <- updateJob store "j2" (\j -> j { qjStatus = Running })
        if updated then deleteJob store "j2" else pure ()
      
      -- Verify job was deleted (update was lost)
      retrieved2 <- atomically $ getJob store "j2"
      retrieved2 `shouldBe` Nothing
      
      -- BUG: This documents that concurrent delete and update can cause lost updates
      -- Solution: Coordinate operations or use conditional updates

  describe "Job Retrieval" $ do
    it "retrieves existing job" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j1" Normal
      atomically $ storeJob store job
      
      retrieved <- atomically $ getJob store "j1"
      retrieved `shouldSatisfy` isJust
      case retrieved of
        Just j -> qjJobId j `shouldBe` "j1"
        Nothing -> expectationFailure "Job should exist"

    it "returns Nothing for non-existent job" $ do
      store <- atomically createJobStore
      
      retrieved <- atomically $ getJob store "nonexistent"
      retrieved `shouldBe` Nothing

    it "retrieves job after update" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j1" Normal
      atomically $ do
        storeJob store job
        updateJob store "j1" (\j -> j { qjStatus = Running })
      
      retrieved <- atomically $ getJob store "j1"
      case retrieved of
        Just j -> qjStatus j `shouldBe` Running
        Nothing -> expectationFailure "Job should exist"

    it "BUG: getJob may return stale data during concurrent update" $ do
      -- BUG: While STM transactions are atomic, if getJob and updateJob are called
      -- in separate transactions, getJob may read state before updateJob completes.
      -- However, STM serializes transactions, so this is prevented in practice.
      -- The real issue is if getJob reads, then updateJob modifies, then getJob's
      -- result is used - the result may be stale.
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j1" Normal
      atomically $ storeJob store job
      
      -- BUG: In separate transactions, getJob may see stale data
      -- Transaction 1: getJob reads job (status = Queued)
      retrieved1 <- atomically $ getJob store "j1"
      case retrieved1 of
        Just j -> qjStatus j `shouldBe` Queued
        Nothing -> expectationFailure "Job should exist"
      
      -- Transaction 2: updateJob modifies job (status = Running)
      updated <- atomically $ updateJob store "j1" (\j -> j { qjStatus = Running })
      updated `shouldBe` True
      
      -- Transaction 3: getJob reads updated job (status = Running)
      retrieved2 <- atomically $ getJob store "j1"
      case retrieved2 of
        Just j -> qjStatus j `shouldBe` Running
        Nothing -> expectationFailure "Job should exist"
      
      -- BUG: retrieved1 contains stale data (status = Queued) even though
      -- job was updated to Running. This is correct STM behavior (snapshot isolation),
      -- but if retrieved1 is used after updateJob, it will have stale data.
      
      -- Verify job was actually updated
      retrieved3 <- atomically $ getJob store "j1"
      case retrieved3 of
        Just j -> qjStatus j `shouldBe` Running
        Nothing -> expectationFailure "Job should exist"
      
      -- BUG: This documents that getJob results can be stale if used after
      -- concurrent updates. Solution: Always read fresh state when needed.

  describe "Job Deletion" $ do
    it "deletes existing job" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j1" Normal
      atomically $ do
        storeJob store job
        deleteJob store "j1"
      
      retrieved <- atomically $ getJob store "j1"
      retrieved `shouldBe` Nothing

    it "deletes job without error if job doesn't exist" $ do
      store <- atomically createJobStore
      
      -- Should not error
      atomically $ deleteJob store "nonexistent"
      
      retrieved <- atomically $ getJob store "nonexistent"
      retrieved `shouldBe` Nothing

    it "deletes only specified job" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job1 = createJob now "j1" Normal
      let job2 = createJob now "j2" Normal
      
      atomically $ do
        storeJob store job1
        storeJob store job2
        deleteJob store "j1"
      
      retrieved1 <- atomically $ getJob store "j1"
      retrieved2 <- atomically $ getJob store "j2"
      
      retrieved1 `shouldBe` Nothing
      retrieved2 `shouldSatisfy` isJust

  describe "Gateway Integration with Job Store" $ do
    it "stores job before processing" $ do
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j1" Normal
      atomically $ do
        storeJob store job
        enqueueJob queue job
      
      -- Process request
      result <- atomically $ processRequest gatewayState
      result `shouldSatisfy` isJust
      
      -- Verify job status updated in store
      retrieved <- atomically $ getJob store "j1"
      case retrieved of
        Just j -> qjStatus j `shouldBe` Running
        Nothing -> expectationFailure "Job should exist"

    it "updates job status to Running when processing starts" $ do
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j1" Normal
      atomically $ do
        storeJob store job
        enqueueJob queue job
      
      -- Process request
      result <- atomically $ processRequest gatewayState
      result `shouldSatisfy` isJust
      
      -- Verify started_at timestamp set
      retrieved <- atomically $ getJob store "j1"
      case retrieved of
        Just j -> qjStartedAt j `shouldSatisfy` isJust
        Nothing -> expectationFailure "Job should exist"

    it "updates job status to Complete on success" $ do
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j1" Normal
      atomically $ storeJob store job
      
      -- Handle success
      atomically $ handleRequestSuccess gatewayState job backend "https://cdn.example.com/output.mp4"
      
      -- Verify job status updated
      retrieved <- atomically $ getJob store "j1"
      case retrieved of
        Just j -> do
          qjStatus j `shouldBe` Complete
          qjOutput j `shouldSatisfy` isJust
          qjCompletedAt j `shouldSatisfy` isJust
        Nothing -> expectationFailure "Job should exist"

    it "updates job status to Error on failure" $ do
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j1" Normal
      atomically $ storeJob store job
      
      -- Handle failure
      atomically $ handleRequestFailure gatewayState job backend "Backend error"
      
      -- Verify job status updated
      retrieved <- atomically $ getJob store "j1"
      case retrieved of
        Just j -> do
          qjStatus j `shouldBe` Error
          qjError j `shouldSatisfy` isJust
          qjCompletedAt j `shouldSatisfy` isJust
        Nothing -> expectationFailure "Job should exist"

    it "handles job deletion during processing" $ do
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j1" Normal
      atomically $ do
        storeJob store job
        enqueueJob queue job
      
      -- Delete job before processing completes
      atomically $ deleteJob store "j1"
      
      -- Process request (should handle deleted job gracefully)
      result <- atomically $ processRequest gatewayState
      -- Result may be Nothing if job was deleted
      -- Backend should be released
      inFlightCount <- atomically $ readTVar (beInFlight backend)
      inFlightCount `shouldBe` 0

    it "BUG: job deletion may not release backend if job is in-flight" $ do
      -- BUG: If a job is deleted while it's being processed (status = Running),
      -- the backend may not be released correctly. Looking at processRequest (line 178-184),
      -- if job is deleted during processing, backend is released. However, if deleteJob
      -- is called after backend selection but before processRequest completes,
      -- backend may not be released.
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      -- Create and enqueue job
      let job = createJob now "j_delete_inflight" Normal
      atomically $ do
        storeJob store job
        enqueueJob queue job
      
      -- Process request (selects backend, increments inFlight)
      result <- atomically $ processRequest gatewayState
      result `shouldSatisfy` isJust
      
      -- Verify backend was selected (inFlight incremented)
      inFlightBefore <- atomically $ readTVar (beInFlight backend)
      inFlightBefore `shouldBe` 1
      
      -- BUG: Delete job while it's being processed (status = Running)
      -- Looking at processRequest (line 178-184), if job is deleted during processing,
      -- backend is released. But if deleteJob is called after processRequest completes
      -- but before handleRequestSuccess/handleRequestFailure, backend may not be released.
      atomically $ deleteJob store "j_delete_inflight"
      
      -- BUG: Backend should be released when job is deleted during processing,
      -- but if deleteJob is called after processRequest, backend may not be released.
      -- This depends on when deleteJob is called relative to processRequest completion.
      
      -- Verify job was deleted
      retrieved <- atomically $ getJob store "j_delete_inflight"
      retrieved `shouldBe` Nothing
      
      -- BUG: Backend inFlight count may still be 1 if deleteJob was called
      -- after backend selection but before backend release.
      -- Solution: Ensure backend is always released when job is deleted,
      -- or track backend association with job and release on deletion.

  describe "Concurrent Operations" $ do
    it "handles concurrent job creation" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let jobs = [createJob now ("j" <> show i) Normal | i <- [1..10]]
      atomically $ mapM_ (storeJob store) jobs
      
      -- All jobs should exist
      retrieved <- atomically $ mapM (getJob store) (map (\i -> "j" <> show i) [1..10])
      all isJust retrieved `shouldBe` True

    it "handles concurrent job updates" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j1" Normal
      atomically $ storeJob store job
      
      -- Update multiple times concurrently
      atomically $ do
        updateJob store "j1" (\j -> j { qjStatus = Running })
        updateJob store "j1" (\j -> j { qjRetryCount = 1 })
      
      retrieved <- atomically $ getJob store "j1"
      case retrieved of
        Just j -> do
          qjStatus j `shouldBe` Running
          qjRetryCount j `shouldBe` 1
        Nothing -> expectationFailure "Job should exist"

    it "BUG: concurrent update and delete may cause inconsistent state" $ do
      -- BUG: If updateJob and deleteJob are called concurrently in separate transactions,
      -- STM serializes them, but the order matters. If delete happens first, update
      -- returns False. If update happens first, delete removes the updated job.
      -- This is correct STM behavior, but documents potential for lost updates.
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j_concurrent" Normal
      atomically $ storeJob store job
      
      -- BUG: Test concurrent update and delete in separate transactions
      -- Transaction 1: Update job
      updated <- atomically $ updateJob store "j_concurrent" (\j -> j { qjStatus = Running })
      updated `shouldBe` True
      
      -- Transaction 2: Delete job (happens after update)
      atomically $ deleteJob store "j_concurrent"
      
      -- BUG: Job was updated then deleted, so update was lost.
      -- This is correct STM behavior (delete wins), but documents that
      -- concurrent update and delete can cause lost updates.
      retrieved <- atomically $ getJob store "j_concurrent"
      retrieved `shouldBe` Nothing
      
      -- Test reverse order (delete then update)
      let job2 = createJob now "j_concurrent2" Normal
      atomically $ storeJob store job2
      
      -- Transaction 1: Delete job
      atomically $ deleteJob store "j_concurrent2"
      
      -- Transaction 2: Update job (happens after delete)
      updated2 <- atomically $ updateJob store "j_concurrent2" (\j -> j { qjStatus = Running })
      updated2 `shouldBe` False  -- Job doesn't exist
      
      -- BUG: Update returned False because job was deleted first.
      -- This is correct STM behavior, but documents that concurrent
      -- update and delete can cause lost updates.
      retrieved2 <- atomically $ getJob store "j_concurrent2"
      retrieved2 `shouldBe` Nothing
      
      -- BUG: This documents that concurrent update and delete can cause
      -- lost updates. Solution: Coordinate operations or use conditional updates.

  describe "Edge Cases" $ do
    it "handles empty job store" $ do
      store <- atomically createJobStore
      
      retrieved <- atomically $ getJob store "any"
      retrieved `shouldBe` Nothing

    it "handles very long job IDs" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let longId = "j_" <> Text.replicate 10000 "a"
      let job = (createJob now longId Normal) { qjJobId = longId }
      atomically $ storeJob store job
      
      retrieved <- atomically $ getJob store longId
      retrieved `shouldSatisfy` isJust

    it "handles unicode in job IDs" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let unicodeId = "j_测试_123"
      let job = (createJob now unicodeId Normal) { qjJobId = unicodeId }
      atomically $ storeJob store job
      
      retrieved <- atomically $ getJob store unicodeId
      retrieved `shouldSatisfy` isJust

    it "handles update with identity function" $ do
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j1" Normal
      atomically $ storeJob store job
      
      -- Update with identity (no change)
      updated <- atomically $ updateJob store "j1" id
      updated `shouldBe` True
      
      retrieved <- atomically $ getJob store "j1"
      retrieved `shouldSatisfy` isJust

  describe "Bug Detection" $ do
    it "BUG: updateJob may fail if job is deleted between lookup and adjust" $ do
      -- BUG: updateJob (line 56-62) reads jobs map, checks if job exists, then adjusts.
      -- Since this is all in one STM transaction, it's atomic. However, if deleteJob
      -- is called in a separate transaction that commits before updateJob, the job
      -- won't exist when updateJob runs, so it returns False.
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j_delete_between" Normal
      atomically $ storeJob store job
      
      -- BUG: In separate transactions, deleteJob may commit before updateJob
      -- Transaction 1: Delete job
      atomically $ deleteJob store "j_delete_between"
      
      -- Transaction 2: Update job (happens after delete)
      updated <- atomically $ updateJob store "j_delete_between" (\j -> j { qjStatus = Running })
      
      -- BUG: updateJob returns False because job was deleted in previous transaction.
      -- This is correct STM behavior (job doesn't exist), but documents that
      -- updateJob can fail if job is deleted between transactions.
      updated `shouldBe` False
      
      -- Verify job was deleted
      retrieved <- atomically $ getJob store "j_delete_between"
      retrieved `shouldBe` Nothing
      
      -- BUG: This documents that updateJob can fail if job is deleted between
      -- transactions. Since STM transactions are atomic, this is correct behavior,
      -- but updateJob callers should handle False return value.
      
      -- Test within same transaction (should work correctly)
      let job2 = createJob now "j_delete_between2" Normal
      atomically $ do
        storeJob store job2
        deleteJob store "j_delete_between2"
        updated2 <- updateJob store "j_delete_between2" (\j -> j { qjStatus = Running })
        -- BUG: updateJob returns False because job was deleted in same transaction
        updated2 `shouldBe` False
      
      -- Verify job was deleted
      retrieved2 <- atomically $ getJob store "j_delete_between2"
      retrieved2 `shouldBe` Nothing
      
      -- BUG: This documents that updateJob correctly handles deleted jobs
      -- by returning False, but callers must handle this case.

    it "BUG: job store may grow unbounded if jobs are never deleted" $ do
      -- BUG: JobStore uses a Map to store jobs (jsJobs :: TVar (Map Text QueuedJob)).
      -- If completed/errored jobs are never deleted, the map grows unbounded,
      -- causing memory leaks in long-running gateways.
      store <- atomically createJobStore
      now <- getCurrentTime
      
      -- Create many completed jobs (simulating long-running gateway)
      let jobCount = 1000
      let jobs = [ (createJob now ("j" <> show i) Normal)
                     { qjStatus = Complete
                     , qjOutput = Just ("output_" <> show i)
                     }
                 | i <- [1..jobCount] ]
      
      -- Store all jobs
      atomically $ mapM_ (storeJob store) jobs
      
      -- Verify all jobs are stored
      allJobs <- atomically $ readTVar (jsJobs store)
      Map.size allJobs `shouldBe` jobCount
      
      -- BUG: Completed jobs are never deleted automatically.
      -- In a long-running gateway processing thousands of jobs per day,
      -- the job store will grow unbounded, consuming increasing memory.
      
      -- Simulate more jobs being added (new requests)
      let newJobs = [ createJob now ("j_new" <> show i) Normal | i <- [1..100] ]
      atomically $ mapM_ (storeJob store) newJobs
      
      -- Verify total job count increased
      allJobsAfter <- atomically $ readTVar (jsJobs store)
      Map.size allJobsAfter `shouldBe` (jobCount + 100)
      
      -- BUG: Job store now contains 1100 jobs, and will continue growing
      -- if completed jobs are never cleaned up. Each job contains:
      -- - Full request body (qjRequest :: Value)
      -- - Output URL (qjOutput :: Maybe Text)
      -- - Error message (qjError :: Maybe Text)
      -- - Timestamps and metadata
      -- This can consume significant memory over time.
      
      -- Solution: Implement TTL-based cleanup or periodic cleanup of completed/errored jobs
      -- Example: Delete jobs older than 24 hours or limit store size

    it "BUG: getJob may return job that was just deleted" $ do
      -- BUG: While STM transactions are atomic, if getJob and deleteJob are called
      -- in separate transactions, getJob may return a job that is deleted immediately
      -- after. However, STM serializes transactions, so this is prevented in practice.
      -- The real issue is if getJob's result is used after deleteJob commits.
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j_get_deleted" Normal
      atomically $ storeJob store job
      
      -- BUG: In separate transactions, getJob may return job that is deleted after
      -- Transaction 1: getJob reads job
      retrieved <- atomically $ getJob store "j_get_deleted"
      retrieved `shouldSatisfy` isJust
      
      -- Transaction 2: deleteJob removes job
      atomically $ deleteJob store "j_get_deleted"
      
      -- BUG: retrieved contains a job that was deleted in a later transaction.
      -- This is correct STM behavior (snapshot isolation), but if retrieved is used
      -- after deleteJob, it will reference a deleted job.
      
      -- Verify job was actually deleted
      retrieved2 <- atomically $ getJob store "j_get_deleted"
      retrieved2 `shouldBe` Nothing
      
      -- BUG: retrieved is stale - it contains a job that no longer exists.
      -- If retrieved is used after deleteJob (e.g., to update job), it will fail
      -- because the job doesn't exist.
      
      -- Test within same transaction (should work correctly)
      let job2 = createJob now "j_get_deleted2" Normal
      atomically $ do
        storeJob store job2
        retrieved3 <- getJob store "j_get_deleted2"
        retrieved3 `shouldSatisfy` isJust
        deleteJob store "j_get_deleted2"
        retrieved4 <- getJob store "j_get_deleted2"
        retrieved4 `shouldBe` Nothing
      
      -- BUG: This documents that getJob results can be stale if used after
      -- concurrent deletes. Solution: Always read fresh state when needed,
      -- or use conditional operations that check job existence.

    it "BUG: updateJob may not be atomic with respect to other operations" $ do
      -- BUG: updateJob (line 56-62) reads jobs map, checks if job exists, then adjusts.
      -- Since this is all in one STM transaction, it's atomic. However, if multiple
      -- updateJob calls happen concurrently in separate transactions, STM serializes them,
      -- but the order matters. Later updates may overwrite earlier updates.
      store <- atomically createJobStore
      now <- getCurrentTime
      
      let job = createJob now "j_atomic" Normal
      atomically $ storeJob store job
      
      -- BUG: Multiple updateJob calls in separate transactions
      -- Transaction 1: Update status to Running
      updated1 <- atomically $ updateJob store "j_atomic" (\j -> j { qjStatus = Running })
      updated1 `shouldBe` True
      
      -- Transaction 2: Update retryCount to 1
      updated2 <- atomically $ updateJob store "j_atomic" (\j -> j { qjRetryCount = 1 })
      updated2 `shouldBe` True
      
      -- Transaction 3: Update status to Complete
      updated3 <- atomically $ updateJob store "j_atomic" (\j -> j { qjStatus = Complete })
      updated3 `shouldBe` True
      
      -- BUG: All updates succeeded, but final state depends on order.
      -- If updates are serialized correctly, final state should have:
      -- - status = Complete (from transaction 3)
      -- - retryCount = 1 (from transaction 2)
      retrieved <- atomically $ getJob store "j_atomic"
      case retrieved of
        Just j -> do
          qjStatus j `shouldBe` Complete
          qjRetryCount j `shouldBe` 1
        Nothing -> expectationFailure "Job should exist"
      
      -- BUG: This documents that multiple updateJob calls may interfere with each other
      -- if they update different fields. Since STM serializes transactions, this is
      -- correct behavior, but callers should be aware that updates may be lost if
      -- multiple updates happen concurrently.
      
      -- Test concurrent updates to same field (last write wins)
      updated4 <- atomically $ updateJob store "j_atomic" (\j -> j { qjStatus = Error })
      updated4 `shouldBe` True
      
      updated5 <- atomically $ updateJob store "j_atomic" (\j -> j { qjStatus = Complete })
      updated5 `shouldBe` True
      
      retrieved2 <- atomically $ getJob store "j_atomic"
      case retrieved2 of
        Just j -> qjStatus j `shouldBe` Complete  -- Last write wins
        Nothing -> expectationFailure "Job should exist"
      
      -- BUG: This documents that concurrent updates to the same field result in
      -- last write winning. Solution: Use conditional updates or coordinate updates.
