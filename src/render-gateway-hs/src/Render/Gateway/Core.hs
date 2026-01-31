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
import Render.Gateway.STM.Queue (RequestQueue, QueuedJob(..), JobStatus(..), dequeueJob, enqueueJob, tryDequeueJob)
import Render.Gateway.STM.RateLimiter (RateLimiter, createRateLimiter, acquireTokenBlocking)
import Render.Gateway.STM.Clock (Clock, readClockSTM)
import Render.Gateway.Backend (Backend, selectBackend, recordBackendSuccess, recordBackendFailure)

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
updateJob :: JobStore -> Text -> (QueuedJob -> QueuedJob) -> STM ()
updateJob JobStore {..} jobId f = do
  modifyTVar' jsJobs (Map.adjust f jobId)

-- | Delete job from job store
deleteJob :: JobStore -> Text -> STM ()
deleteJob JobStore {..} jobId = do
  modifyTVar' jsJobs (Map.delete jobId)

-- | Get queue position for a job
getQueuePosition :: RequestQueue -> Text -> STM Int
getQueuePosition _queue _jobId = do
  -- For now, return a placeholder
  -- Real implementation would scan the queues
  pure 0

-- | Process request atomically
-- | Returns Nothing if no backend available (job stays in queue)
processRequest :: GatewayState -> STM (Maybe (QueuedJob, Backend))
processRequest GatewayState {..} = do
  -- Try to dequeue job (non-blocking)
  mJob <- tryDequeueJob gsQueue

  case mJob of
    Nothing -> pure Nothing
    Just job -> do
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
          -- No backend available, requeue job
          enqueueJob gsQueue job
          pure Nothing
        Just b -> do
          -- Update job status to Running
          updateJob gsJobStore (qjJobId job) (\j -> j { qjStatus = Running })
          pure (Just (job, b))

-- | Handle request completion
handleRequestSuccess :: GatewayState -> QueuedJob -> Backend -> Text -> STM ()
handleRequestSuccess GatewayState {..} job backend outputUrl = do
  recordBackendSuccess backend
  -- Update job status to Complete with output URL
  updateJob gsJobStore (qjJobId job) (\j -> j
    { qjStatus = Complete
    , qjOutput = Just outputUrl
    })

-- | Handle request failure
handleRequestFailure :: GatewayState -> QueuedJob -> Backend -> Text -> STM ()
handleRequestFailure GatewayState {..} job backend errorMsg = do
  (_, now) <- readClockSTM gsClock
  recordBackendFailure backend now
  -- Update job status to Error
  updateJob gsJobStore (qjJobId job) (\j -> j
    { qjStatus = Error
    , qjError = Just errorMsg
    })

-- | Cancel a job
cancelJob :: GatewayState -> Text -> STM Bool
cancelJob GatewayState {..} jobId = do
  mJob <- getJob gsJobStore jobId
  case mJob of
    Nothing -> pure False
    Just job -> do
      case qjStatus job of
        Queued -> do
          -- Mark as cancelled
          updateJob gsJobStore jobId (\j -> j { qjStatus = Cancelled })
          pure True
        Running -> do
          -- Can't cancel running job easily, but mark it
          updateJob gsJobStore jobId (\j -> j { qjStatus = Cancelled })
          pure True
        _ -> pure False -- Already complete/error/cancelled
