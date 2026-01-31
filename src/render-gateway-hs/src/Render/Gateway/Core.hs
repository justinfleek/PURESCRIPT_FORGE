{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}

-- | Render Gateway Core
-- | Main gateway logic composing queue, rate limiter, and backend selection
module Render.Gateway.Core where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Control.Monad (unless)
import Data.Time (UTCTime)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Render.Gateway.STM.Queue (RequestQueue, QueuedJob, dequeueJob, enqueueJob)
import Render.Gateway.STM.RateLimiter (RateLimiter, createRateLimiter, acquireTokenBlocking)
import Render.Gateway.STM.Clock (Clock, readClockSTM)
import Render.Gateway.Backend (Backend, selectBackend, recordBackendSuccess, recordBackendFailure)

-- | Gateway state
data GatewayState = GatewayState
  { gsQueue :: RequestQueue
  , gsRateLimiters :: TVar (Map String RateLimiter) -- customer_id -> rate limiter
  , gsBackends :: [Backend]
  , gsClock :: Clock
  }

-- | Process request atomically
processRequest :: GatewayState -> STM (Maybe (QueuedJob, Backend))
processRequest GatewayState {..} = do
  -- Dequeue job
  job <- dequeueJob gsQueue
  
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
  backend <- selectBackend gsBackends (qjModelFamily job) (qjModelName job) gsClock
  
  case backend of
    Nothing -> do
      -- No backend available, requeue job
      enqueueJob gsQueue job
      retry -- atomic rollback
    Just b -> pure (Just (job, b))

-- | Handle request completion
handleRequestSuccess :: GatewayState -> QueuedJob -> Backend -> STM ()
handleRequestSuccess GatewayState {..} job backend = do
  recordBackendSuccess backend

-- | Handle request failure
handleRequestFailure :: GatewayState -> QueuedJob -> Backend -> STM ()
handleRequestFailure GatewayState {..} job backend = do
  (_, now) <- readClockSTM gsClock
  recordBackendFailure backend now
  -- Optionally requeue job with lower priority
  -- enqueueJob gsQueue (job { qjPriority = Low })
