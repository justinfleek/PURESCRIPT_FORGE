{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Render Gateway Core
-- | Main gateway logic composing queue, rate limiter, backend selection, and job store
module Render.Gateway.Core where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (findIndex)
import Render.Gateway.STM.Queue (RequestQueue(..), QueuedJob(..), JobStatus(..), dequeueJob, enqueueJob, tryDequeueJob)
import Control.Concurrent.STM.TQueue (isEmptyTQueue, readTQueue, writeTQueue)
import Render.Gateway.STM.RateLimiter (RateLimiter, createRateLimiter, acquireTokenBlocking)
import Render.Gateway.STM.Clock (Clock, readClockSTM)
import Render.Gateway.Backend (Backend, selectBackend, recordBackendSuccess, recordBackendFailure, releaseBackend)

-- | Job store for tracking job status
data JobStore = JobStore
  { jsJobs :: TVar (Map Text QueuedJob)  -- job_id -> job
  }

-- | Create empty job store
createJobStore :: STM JobStore
createJobStore = do
  jobs <- newTVar Map.empty
  pure JobStore { jsJobs = jobs }

-- | Gateway state
data GatewayState = GatewayState
  { gsQueue :: RequestQueue
  , gsJobStore :: JobStore
  , gsRateLimiters :: TVar (Map Text RateLimiter) -- customer_id -> rate limiter
  , gsBackends :: [Backend]
  , gsClock :: Clock
  }

-- | Store job in job store
storeJob :: JobStore -> QueuedJob -> STM ()
storeJob JobStore {..} job = do
  modifyTVar' jsJobs (Map.insert (qjJobId job) job)

-- | Get job from job store
getJob :: JobStore -> Text -> STM (Maybe QueuedJob)
getJob JobStore {..} jobId = do
  jobs <- readTVar jsJobs
  pure (Map.lookup jobId jobs)

-- | Update job in job store
-- | Returns True if job was updated, False if job doesn't exist
updateJob :: JobStore -> Text -> (QueuedJob -> QueuedJob) -> STM Bool
updateJob JobStore {..} jobId f = do
  jobs <- readTVar jsJobs
  case Map.lookup jobId jobs of
    Nothing -> pure False
    Just _ -> do
      modifyTVar' jsJobs (Map.adjust f jobId)
      pure True

-- | Delete job from job store
deleteJob :: JobStore -> Text -> STM ()
deleteJob JobStore {..} jobId = do
  modifyTVar' jsJobs (Map.delete jobId)

-- | Drain queue to list (consumes queue)
-- | Helper function for queue scanning operations
drainQueueToList :: TQueue QueuedJob -> STM [QueuedJob]
drainQueueToList q = do
  isEmpty <- isEmptyTQueue q
  if isEmpty
    then pure []
    else do
      job <- readTQueue q
      rest <- drainQueueToList q
      pure (job : rest)

-- | Get queue position for a job
-- | 
-- | Note: This scans queues by temporarily draining and re-enqueuing.
-- | This operation is atomic within STM, but is not atomic with respect to
-- | concurrent `tryDequeueJob` operations. If a job is dequeued concurrently
-- | while scanning, the position may be incorrect or the job may not be found.
-- | 
-- | This is an acceptable limitation for approximate position display.
-- | For exact positions, consider maintaining a position map separately.
getQueuePosition :: RequestQueue -> Text -> STM Int
getQueuePosition queue jobId = do
  -- Scan high priority queue first
  highPos <- scanQueue (rqHigh queue) jobId
  case highPos of
    Just pos -> pure pos
    Nothing -> do
      -- Scan normal priority queue
      normalPos <- scanQueue (rqNormal queue) jobId
      case normalPos of
        Just pos -> do
          highLen <- getQueueLength (rqHigh queue)
          pure (highLen + pos)
        Nothing -> do
          -- Scan low priority queue
          lowPos <- scanQueue (rqLow queue) jobId
          case lowPos of
            Just pos -> do
              highLen <- getQueueLength (rqHigh queue)
              normalLen <- getQueueLength (rqNormal queue)
              pure (highLen + normalLen + pos)
            Nothing -> pure (-1) -- Job not found in queue
  where
    -- Scan queue by draining into a list, finding position, then re-enqueuing
    scanQueue :: TQueue QueuedJob -> Text -> STM (Maybe Int)
    scanQueue q jobId = do
      -- Drain queue into list
      jobs <- drainQueueToList q
      -- Find position
      let pos = findIndex (\j -> qjJobId j == jobId) jobs
      -- Re-enqueue all jobs (preserving order)
      mapM_ (writeTQueue q) jobs
      pure pos
    
    -- Get queue length by draining and re-enqueuing
    getQueueLength :: TQueue QueuedJob -> STM Int
    getQueueLength q = do
      jobs <- drainQueueToList q
      mapM_ (writeTQueue q) jobs
      pure (length jobs)

-- | Process request atomically
-- | Returns Nothing if no backend available (job stays in queue)
processRequest :: GatewayState -> STM (Maybe (QueuedJob, Backend))
processRequest GatewayState {..} = do
  -- Try to dequeue job (non-blocking)
  mJob <- tryDequeueJob gsQueue

  case mJob of
    Nothing -> pure Nothing
    Just job -> do
      -- Filter out cancelled jobs immediately after dequeueing
      -- If cancelled, don't process but counter was already decremented (correct - cancelled job removed)
      if qjStatus job == Cancelled
        then pure Nothing -- Don't process cancelled jobs
        else do
          -- Get or create rate limiter for customer
          limiters <- readTVar gsRateLimiters
          let customerId = qjCustomerId job
          rateLimiter <- case Map.lookup customerId limiters of
            Just rl -> pure rl
            Nothing -> do
              -- Create default rate limiter (100 req/s, 1000 capacity)
              (_, now) <- readClockSTM gsClock
              rl <- createRateLimiter 1000.0 100.0 now
              modifyTVar' gsRateLimiters (Map.insert customerId rl)
              pure rl

          -- Acquire rate limit token (blocking with retry)
          acquireTokenBlocking rateLimiter gsClock

          -- Select backend
          backend <- selectBackend gsBackends (qjModelFamily job) (qjModelName job) (qjBackend job) gsClock

          case backend of
            Nothing -> do
              -- No backend available, requeue job (only if not cancelled)
              -- Note: job status already checked above, but check again in case it was cancelled concurrently
              currentJob <- getJob gsJobStore (qjJobId job)
              case currentJob of
                Nothing -> pure Nothing -- Job was deleted
                Just j -> if qjStatus j == Cancelled
                  then pure Nothing -- Job was cancelled, don't requeue
                  else do
                    enqueueJob gsQueue j -- Use current job state
                    pure Nothing
            Just b -> do
              -- Check if job was cancelled before marking as running
              currentJob <- getJob gsJobStore (qjJobId job)
              case currentJob of
                Nothing -> do
                  -- Job was deleted, release backend (decrement in-flight counter)
                  -- Backend was already incremented by selectBackend, so we must decrement
                  releaseBackend b
                  pure Nothing
                Just j -> if qjStatus j == Cancelled
                  then do
                    -- Job was cancelled, release backend (decrement in-flight counter)
                    releaseBackend b
                    pure Nothing -- Don't process cancelled jobs
                  else do
                    -- Update job status to Running and set started_at timestamp
                    (_, now) <- readClockSTM gsClock
                    updated <- updateJob gsJobStore (qjJobId job) (\job' -> job'
                      { qjStatus = Running
                      , qjStartedAt = Just now
                      })
                    if updated
                      then pure (Just (j, b)) -- Use current job state
                      else do
                        -- Job was deleted during update, release backend
                        releaseBackend b
                        pure Nothing

-- | Handle request completion
-- | Checks if job was cancelled before marking as complete
handleRequestSuccess :: GatewayState -> QueuedJob -> Backend -> Text -> STM ()
handleRequestSuccess GatewayState {..} job backend outputUrl = do
  -- Check if job was cancelled before marking as complete
  mCurrentJob <- getJob gsJobStore (qjJobId job)
  case mCurrentJob of
    Nothing -> pure () -- Job was deleted, ignore
    Just currentJob ->
      if qjStatus currentJob == Cancelled
        then pure () -- Job was cancelled, ignore result
        else do
          -- Update job status to Complete with output URL and completed_at timestamp
          (_, now) <- readClockSTM gsClock
          updated <- updateJob gsJobStore (qjJobId job) (\j -> j
            { qjStatus = Complete
            , qjOutput = Just outputUrl
            , qjCompletedAt = Just now
            })
          -- Only record backend success if job update succeeded
          -- This prevents backend stats from being updated if job was deleted between check and update
          if updated
            then recordBackendSuccess backend now
            else pure () -- Job was deleted during update, ignore

-- | Handle request failure
-- | Checks if job was cancelled before marking as error
handleRequestFailure :: GatewayState -> QueuedJob -> Backend -> Text -> STM ()
handleRequestFailure GatewayState {..} job backend errorMsg = do
  -- Check if job was cancelled before marking as error
  mCurrentJob <- getJob gsJobStore (qjJobId job)
  case mCurrentJob of
    Nothing -> pure () -- Job was deleted, ignore
    Just currentJob ->
      if qjStatus currentJob == Cancelled
        then pure () -- Job was cancelled, ignore result
        else do
          (_, now) <- readClockSTM gsClock
          -- Update job status to Error with completed_at timestamp
          updated <- updateJob gsJobStore (qjJobId job) (\j -> j
            { qjStatus = Error
            , qjError = Just errorMsg
            , qjCompletedAt = Just now
            })
          -- Only record backend failure if job update succeeded
          -- This prevents backend stats from being updated if job was deleted between check and update
          if updated
            then recordBackendFailure backend now
            else pure () -- Job was deleted during update, ignore

-- | Cancel a job
-- | For queued jobs: removes from queue and marks as cancelled
-- | For running jobs: marks as cancelled (HTTP request will complete but result will be ignored)
-- | Returns True if job was successfully cancelled, False if job not found or already terminal
cancelJob :: GatewayState -> Text -> STM Bool
cancelJob GatewayState {..} jobId = do
  mJob <- getJob gsJobStore jobId
  case mJob of
    Nothing -> pure False
    Just job -> do
      case qjStatus job of
        Queued -> do
          -- Remove job from queue and mark as cancelled
          -- Scan queues to find and remove the job
          -- Note: If job is already dequeued (being processed), removal will fail
          -- but we still want to mark it as cancelled
          removed <- removeJobFromQueue gsQueue jobId
          updated <- updateJob gsJobStore jobId (\j -> j { qjStatus = Cancelled })
          -- Return True if job was successfully marked as cancelled
          -- Removal may fail if job was already dequeued, which is acceptable
          pure updated
        Running -> do
          -- Mark as cancelled (processJobAsync will check and ignore result)
          -- Note: HTTP request in flight cannot be cancelled without async exceptions
          -- The result will be checked and ignored if job is cancelled
          updated <- updateJob gsJobStore jobId (\j -> j { qjStatus = Cancelled })
          pure updated
        _ -> pure False -- Already complete/error/cancelled

-- | Remove a job from the queue by scanning and filtering
-- | Returns True if job was found and removed, False otherwise
-- | Note: This operation is atomic within STM, but if the job was concurrently
-- | dequeued by tryDequeueJob, it may not be found in the queue. This is acceptable
-- | as the job is already removed and rqSize already decremented by tryDequeueJob.
removeJobFromQueue :: RequestQueue -> Text -> STM Bool
removeJobFromQueue RequestQueue {..} jobId = do
  -- Try high priority queue first
  highRemoved <- removeFromQueue rqHigh jobId
  if highRemoved
    then do
      -- Only decrement rqSize if job was actually found and removed
      -- If job was concurrently dequeued, removeFromQueue returns False and we don't decrement
      modifyTVar' rqSize (\n -> max 0 (n - 1))
      pure True
    else do
      -- Try normal priority queue
      normalRemoved <- removeFromQueue rqNormal jobId
      if normalRemoved
        then do
          modifyTVar' rqSize (\n -> max 0 (n - 1))
          pure True
        else do
          -- Try low priority queue
          lowRemoved <- removeFromQueue rqLow jobId
          if lowRemoved
            then do
              modifyTVar' rqSize (\n -> max 0 (n - 1))
              pure True
            else pure False
  where
    -- Remove job from a specific queue by draining, filtering, and re-enqueuing
    -- Returns True if job was found and removed, False if job not found
    -- Note: If job was concurrently dequeued, this will return False (job not in drained list)
    removeFromQueue :: TQueue QueuedJob -> Text -> STM Bool
    removeFromQueue q jobId = do
      -- Drain queue into list (atomic operation)
      jobs <- drainQueueToList q
      -- Check if job exists
      let (before, after) = break (\j -> qjJobId j == jobId) jobs
      case after of
        [] -> do
          -- Job not found (may have been concurrently dequeued)
          -- Re-enqueue all jobs (preserving order)
          mapM_ (writeTQueue q) jobs
          pure False
        (_ : rest) -> do
          -- Job found, re-enqueue all except the removed job
          mapM_ (writeTQueue q) (before ++ rest)
          pure True
