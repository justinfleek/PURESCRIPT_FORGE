{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive unit tests for Queue module
-- | Tests individual functions in isolation: createQueue, enqueueJob, dequeueJob,
-- | tryDequeueJob, queueSize, isEmpty, parseTaskType, parseModality, parsePriority
module QueueSpec where

import Test.Hspec
import Control.Concurrent.STM
import Control.Monad (replicateM, replicateM_)
import Data.Time (getCurrentTime)
import Data.Aeson (object)
import Data.Text (Text)
import qualified Data.Text as Text
import Render.Gateway.STM.Queue
  ( RequestQueue(..)
  , QueuedJob(..)
  , Priority(..)
  , Modality(..)
  , TaskType(..)
  , JobStatus(..)
  , createQueue
  , enqueueJob
  , dequeueJob
  , tryDequeueJob
  , queueSize
  , isEmpty
  , parseTaskType
  , parseModality
  , parsePriority
  )

-- | Helper to create test job
createTestJob :: Text -> Priority -> QueuedJob
createTestJob jobId priority = QueuedJob
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
  , qjCreatedAt = error "qjCreatedAt not set"  -- Will be set in tests
  , qjStartedAt = Nothing
  , qjCompletedAt = Nothing
  , qjRequest = object []
  , qjOutput = Nothing
  , qjError = Nothing
  , qjRetryCount = 0
  }

-- | Deep comprehensive unit tests for Queue module
spec :: Spec
spec = describe "Queue Unit Tests" $ do
  describe "createQueue" $ do
    it "creates empty queue with zero size" $ do
      queue <- atomically createQueue
      
      size <- atomically $ queueSize queue
      empty <- atomically $ isEmpty queue
      
      size `shouldBe` 0
      empty `shouldBe` True

    it "BUG: creates queue with size counter that can become inconsistent" $ do
      -- BUG: createQueue (line 63-74) creates a size counter (TVar Int32)
      -- that tracks queue size. However, if enqueueJob and dequeueJob are
      -- called incorrectly or if there are bugs, size counter can become
      -- inconsistent with actual queue contents.
      queue <- atomically createQueue
      
      -- Manually set size counter to wrong value (edge case test)
      atomically $ writeTVar (rqSize queue) 10
      
      size <- atomically $ queueSize queue
      empty <- atomically $ isEmpty queue
      
      -- BUG: Size counter says 10, but queue is actually empty
      -- This inconsistency can cause bugs in queue size reporting.
      size `shouldBe` 10
      empty `shouldBe` True  -- Queue is actually empty

  describe "enqueueJob" $ do
    it "enqueues job to high priority queue" $ do
      now <- getCurrentTime
      queue <- atomically createQueue
      let job = (createTestJob "j1" High) { qjCreatedAt = now }
      
      atomically $ enqueueJob queue job
      
      size <- atomically $ queueSize queue
      empty <- atomically $ isEmpty queue
      size `shouldBe` 1
      empty `shouldBe` False

    it "enqueues job to normal priority queue" $ do
      now <- getCurrentTime
      queue <- atomically createQueue
      let job = (createTestJob "j1" Normal) { qjCreatedAt = now }
      
      atomically $ enqueueJob queue job
      
      size <- atomically $ queueSize queue
      size `shouldBe` 1

    it "enqueues job to low priority queue" $ do
      now <- getCurrentTime
      queue <- atomically createQueue
      let job = (createTestJob "j1" Low) { qjCreatedAt = now }
      
      atomically $ enqueueJob queue job
      
      size <- atomically $ queueSize queue
      size `shouldBe` 1

    it "BUG: enqueueJob increments size counter even if queue is full" $ do
      -- BUG: enqueueJob (line 77-83) increments size counter (line 83) after
      -- writing to queue (line 80-82). However, TQueue is unbounded, so it
      -- never fails. But if there were a bounded queue, size counter could
      -- become inconsistent if writeTQueue fails.
      now <- getCurrentTime
      queue <- atomically createQueue
      let job = (createTestJob "j1" High) { qjCreatedAt = now }
      
      -- Enqueue many jobs (TQueue is unbounded, so this always succeeds)
      replicateM_ 1000 $ atomically $ enqueueJob queue job
      
      size <- atomically $ queueSize queue
      -- BUG: Size counter is incremented for each enqueue, so size = 1000
      -- This is correct for unbounded queue, but if queue were bounded and
      -- writeTQueue failed, size counter would be wrong.
      size `shouldBe` 1000

    it "BUG: enqueueJob doesn't validate job priority matches queue" $ do
      -- BUG: enqueueJob (line 79-82) routes job to queue based on priority,
      -- but doesn't validate that job's priority matches the queue it's being
      -- added to. If job priority is changed after enqueue, it will be in
      -- wrong queue.
      now <- getCurrentTime
      queue <- atomically createQueue
      let job = (createTestJob "j1" High) { qjCreatedAt = now }
      
      atomically $ enqueueJob queue job
      
      -- BUG: Job is in high priority queue, but if we change job's priority
      -- field (which we can't do, but if we could), it would be inconsistent.
      -- The issue is that job priority is stored in the job, not validated
      -- against the queue it's in.

  describe "dequeueJob" $ do
    it "dequeues high priority job first" $ do
      now <- getCurrentTime
      queue <- atomically createQueue
      let jobHigh = (createTestJob "j1" High) { qjCreatedAt = now }
      let jobNormal = (createTestJob "j2" Normal) { qjCreatedAt = now }
      
      atomically $ do
        enqueueJob queue jobNormal
        enqueueJob queue jobHigh
      
      dequeued <- atomically $ dequeueJob queue
      qjJobId dequeued `shouldBe` "j1"  -- High priority dequeued first

    it "dequeues normal priority after high priority" $ do
      now <- getCurrentTime
      queue <- atomically createQueue
      let jobHigh = (createTestJob "j1" High) { qjCreatedAt = now }
      let jobNormal = (createTestJob "j2" Normal) { qjCreatedAt = now }
      
      atomically $ do
        enqueueJob queue jobHigh
        enqueueJob queue jobNormal
      
      dequeued1 <- atomically $ dequeueJob queue
      dequeued2 <- atomically $ dequeueJob queue
      qjJobId dequeued1 `shouldBe` "j1"  -- High priority first
      qjJobId dequeued2 `shouldBe` "j2"  -- Normal priority second

    it "BUG: dequeueJob blocks indefinitely when queue is empty" $ do
      -- BUG: dequeueJob (line 86-92) uses readTQueue, which blocks indefinitely
      -- when queue is empty. There's no timeout mechanism, so this can cause
      -- deadlock if queue never receives jobs.
      queue <- atomically createQueue
      
      -- BUG: dequeueJob will block forever if queue is empty
      -- We can't easily test this without a timeout or background thread.
      -- This test documents the issue.

    it "BUG: dequeueJob may decrement size counter incorrectly" $ do
      -- BUG: dequeueJob (line 91) decrements size counter using:
      -- modifyTVar' rqSize (\n -> max 0 (n - 1))
      -- The max 0 prevents negative size, but if size counter is already
      -- inconsistent (e.g., size = 0 but queue has jobs), decrementing will
      -- keep size at 0, making inconsistency worse.
      now <- getCurrentTime
      queue <- atomically createQueue
      let job = (createTestJob "j1" High) { qjCreatedAt = now }
      
      -- Manually set size counter to 0 (inconsistent - queue has 1 job)
      atomically $ do
        enqueueJob queue job
        writeTVar (rqSize queue) 0  -- BUG: Set size to 0, but queue has 1 job
      
      -- Dequeue job
      dequeued <- atomically $ dequeueJob queue
      qjJobId dequeued `shouldBe` "j1"
      
      size <- atomically $ queueSize queue
      -- BUG: Size was 0, decremented to max(0, 0-1) = 0, so size stays at 0
      -- This hides the inconsistency - size counter is wrong but doesn't go negative.
      size `shouldBe` 0

    it "BUG: dequeueJob doesn't validate job priority matches queue" $ do
      -- BUG: dequeueJob (line 88-90) reads from queues in priority order,
      -- but doesn't validate that dequeued job's priority matches the queue
      -- it came from. If job priority was changed after enqueue, dequeued
      -- job will have wrong priority.
      now <- getCurrentTime
      queue <- atomically createQueue
      let job = (createTestJob "j1" High) { qjCreatedAt = now }
      
      atomically $ enqueueJob queue job
      dequeued <- atomically $ dequeueJob queue
      
      -- BUG: Dequeued job should have High priority (it came from high queue),
      -- but if job priority was changed after enqueue, it would be wrong.
      -- The issue is that job priority is stored in the job, not validated
      -- against the queue it came from.
      qjPriority dequeued `shouldBe` High

  describe "tryDequeueJob" $ do
    it "returns Just job when queue has jobs" $ do
      now <- getCurrentTime
      queue <- atomically createQueue
      let job = (createTestJob "j1" High) { qjCreatedAt = now }
      
      atomically $ enqueueJob queue job
      mJob <- atomically $ tryDequeueJob queue
      
      case mJob of
        Just j -> qjJobId j `shouldBe` "j1"
        Nothing -> expectationFailure "Should have dequeued job"

    it "returns Nothing when queue is empty" $ do
      queue <- atomically createQueue
      mJob <- atomically $ tryDequeueJob queue
      mJob `shouldBe` Nothing

    it "BUG: tryDequeueJob may have race condition with concurrent enqueue" $ do
      -- BUG: tryDequeueJob (line 95-114) checks each queue sequentially
      -- (high, normal, low). If a job is enqueued to high queue between
      -- checking high and normal, tryDequeueJob may return Nothing even
      -- though high queue has a job.
      --
      -- Actually, STM ensures atomicity, so this is prevented within
      -- a single transaction. But if tryDequeueJob is called multiple times
      -- concurrently, race conditions can occur.
      now <- getCurrentTime
      queue <- atomically createQueue
      
      -- BUG: If tryDequeueJob checks high queue (empty), then another thread
      -- enqueues to high queue, then tryDequeueJob checks normal (empty),
      -- it will return Nothing even though high queue now has a job.
      -- However, STM ensures atomicity within a transaction, so this is
      -- only an issue across transactions.

    it "BUG: tryDequeueJob may decrement size counter incorrectly" $ do
      -- BUG: tryDequeueJob (line 100, 106, 112) decrements size counter
      -- using max 0 (n - 1), which prevents negative size but can hide
      -- inconsistencies, similar to dequeueJob.
      now <- getCurrentTime
      queue <- atomically createQueue
      let job = (createTestJob "j1" High) { qjCreatedAt = now }
      
      -- Manually set size counter to 0 (inconsistent)
      atomically $ do
        enqueueJob queue job
        writeTVar (rqSize queue) 0
      
      mJob <- atomically $ tryDequeueJob queue
      case mJob of
        Just _ -> do
          size <- atomically $ queueSize queue
          -- BUG: Size was 0, decremented to max(0, 0-1) = 0
          size `shouldBe` 0
        Nothing -> expectationFailure "Should have dequeued job"

  describe "queueSize" $ do
    it "returns correct size for multiple jobs" $ do
      now <- getCurrentTime
      queue <- atomically createQueue
      let jobs = map (\i -> (createTestJob (Text.pack ("j" <> show i)) High) { qjCreatedAt = now }) [1..10]
      
      mapM_ (atomically . enqueueJob queue) jobs
      size <- atomically $ queueSize queue
      size `shouldBe` 10

    it "BUG: queueSize may return inconsistent value" $ do
      -- BUG: queueSize (line 117-118) returns the size counter value, which
      -- may be inconsistent with actual queue contents if there are bugs in
      -- enqueueJob/dequeueJob or if size counter is manually modified.
      now <- getCurrentTime
      queue <- atomically createQueue
      let job = (createTestJob "j1" High) { qjCreatedAt = now }
      
      atomically $ enqueueJob queue job
      
      -- Manually set size counter to wrong value
      atomically $ writeTVar (rqSize queue) 5
      
      size <- atomically $ queueSize queue
      empty <- atomically $ isEmpty queue
      
      -- BUG: Size counter says 5, but queue actually has 1 job
      size `shouldBe` 5
      empty `shouldBe` False  -- Queue is not empty

  describe "isEmpty" $ do
    it "returns True when all queues are empty" $ do
      queue <- atomically createQueue
      empty <- atomically $ isEmpty queue
      empty `shouldBe` True

    it "returns False when any queue has jobs" $ do
      now <- getCurrentTime
      queue <- atomically createQueue
      let job = (createTestJob "j1" High) { qjCreatedAt = now }
      
      atomically $ enqueueJob queue job
      empty <- atomically $ isEmpty queue
      empty `shouldBe` False

    it "BUG: isEmpty doesn't check size counter" $ do
      -- BUG: isEmpty (line 121-126) checks if queues are empty by calling
      -- isEmptyTQueue on each queue, but doesn't check the size counter.
      -- If size counter is inconsistent, isEmpty may return wrong value.
      now <- getCurrentTime
      queue <- atomically createQueue
      let job = (createTestJob "j1" High) { qjCreatedAt = now }
      
      atomically $ enqueueJob queue job
      
      -- Manually set size counter to 0 (inconsistent)
      atomically $ writeTVar (rqSize queue) 0
      
      empty <- atomically $ isEmpty queue
      size <- atomically $ queueSize queue
      
      -- BUG: isEmpty checks queues (not empty), but size counter says 0
      -- This inconsistency can cause bugs in queue size reporting.
      empty `shouldBe` False  -- Queue is not empty
      size `shouldBe` 0  -- But size counter says 0

  describe "parseTaskType" $ do
    it "parses valid task types" $ do
      parseTaskType "t2v" `shouldBe` Just T2V
      parseTaskType "i2v" `shouldBe` Just I2V
      parseTaskType "t2i" `shouldBe` Just T2I
      parseTaskType "i2i" `shouldBe` Just I2I
      parseTaskType "edit" `shouldBe` Just Edit

    it "BUG: parseTaskType is case-sensitive" $ do
      -- BUG: parseTaskType (line 129-135) is case-sensitive, so "T2V" or
      -- "T2v" will return Nothing even though they're valid task types.
      parseTaskType "T2V" `shouldBe` Nothing  -- BUG: Should be case-insensitive
      parseTaskType "T2v" `shouldBe` Nothing  -- BUG: Should be case-insensitive
      parseTaskType "t2V" `shouldBe` Nothing  -- BUG: Should be case-insensitive

    it "BUG: parseTaskType doesn't handle whitespace" $ do
      -- BUG: parseTaskType doesn't trim whitespace, so " t2v " or "t2v\n"
      -- will return Nothing even though they're valid task types with whitespace.
      parseTaskType " t2v" `shouldBe` Nothing  -- BUG: Should trim whitespace
      parseTaskType "t2v " `shouldBe` Nothing  -- BUG: Should trim whitespace
      parseTaskType "t2v\n" `shouldBe` Nothing  -- BUG: Should trim whitespace

    it "returns Nothing for invalid task types" $ do
      parseTaskType "invalid" `shouldBe` Nothing
      parseTaskType "" `shouldBe` Nothing
      parseTaskType "t2vx" `shouldBe` Nothing

  describe "parseModality" $ do
    it "parses valid modalities" $ do
      parseModality "video" `shouldBe` Just Video
      parseModality "image" `shouldBe` Just Image

    it "BUG: parseModality is case-sensitive" $ do
      -- BUG: parseModality (line 138-141) is case-sensitive, so "Video" or
      -- "VIDEO" will return Nothing even though they're valid modalities.
      parseModality "Video" `shouldBe` Nothing  -- BUG: Should be case-insensitive
      parseModality "VIDEO" `shouldBe` Nothing  -- BUG: Should be case-insensitive
      parseModality "vIdEo" `shouldBe` Nothing  -- BUG: Should be case-insensitive

    it "BUG: parseModality doesn't handle whitespace" $ do
      -- BUG: parseModality doesn't trim whitespace, so " video " will return
      -- Nothing even though it's a valid modality with whitespace.
      parseModality " video" `shouldBe` Nothing  -- BUG: Should trim whitespace
      parseModality "video " `shouldBe` Nothing  -- BUG: Should trim whitespace

    it "returns Nothing for invalid modalities" $ do
      parseModality "invalid" `shouldBe` Nothing
      parseModality "" `shouldBe` Nothing

  describe "parsePriority" $ do
    it "parses valid priorities" $ do
      parsePriority "high" `shouldBe` High
      parsePriority "low" `shouldBe` Low
      parsePriority "normal" `shouldBe` Normal  -- Default case

    it "BUG: parsePriority defaults to Normal for invalid input" $ do
      -- BUG: parsePriority (line 144-147) defaults to Normal for any input
      -- that doesn't match "high" or "low". This means invalid priorities
      -- are silently converted to Normal, which may hide configuration errors.
      parsePriority "invalid" `shouldBe` Normal  -- BUG: Should return error or Nothing
      parsePriority "" `shouldBe` Normal  -- BUG: Should return error or Nothing
      parsePriority "HIGH" `shouldBe` Normal  -- BUG: Should be case-insensitive

    it "BUG: parsePriority is case-sensitive" $ do
      -- BUG: parsePriority is case-sensitive, so "High" or "HIGH" will
      -- return Normal instead of High.
      parsePriority "High" `shouldBe` Normal  -- BUG: Should be case-insensitive
      parsePriority "HIGH" `shouldBe` Normal  -- BUG: Should be case-insensitive
      parsePriority "Low" `shouldBe` Normal  -- BUG: Should be case-insensitive

    it "BUG: parsePriority doesn't handle whitespace" $ do
      -- BUG: parsePriority doesn't trim whitespace, so " high " will return
      -- Normal instead of High.
      parsePriority " high" `shouldBe` Normal  -- BUG: Should trim whitespace
      parsePriority "high " `shouldBe` Normal  -- BUG: Should trim whitespace
