{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}

-- | Render Gateway STM Priority Queue
-- | Three-lane priority queue with O(1) operations
module Render.Gateway.STM.Queue where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Data.Int (Int32)
import Data.Time (UTCTime)

-- | Queued job
data QueuedJob = QueuedJob
  { qjRequestId :: String
  , qjCustomerId :: String
  , qjModelFamily :: String
  , qjModelName :: String
  , qjTask :: String
  , qjPriority :: Priority
  , qjCreatedAt :: UTCTime
  , qjRequest :: String -- JSON request body
  }

-- | Priority level
data Priority = High | Normal | Low
  deriving (Eq, Ord, Show)

-- | Request queue with three priority lanes
data RequestQueue = RequestQueue
  { rqHigh :: TQueue QueuedJob
  , rqNormal :: TQueue QueuedJob
  , rqLow :: TQueue QueuedJob
  , rqSize :: TVar Int32
  }

-- | Create empty request queue
createQueue :: STM RequestQueue
createQueue = do
  high <- newTQueue
  normal <- newTQueue
  low <- newTQueue
  size <- newTVar 0
  pure RequestQueue
    { rqHigh = high
    , rqNormal = normal
    , rqLow = low
    , rqSize = size
    }

-- | Enqueue job with priority
enqueueJob :: RequestQueue -> QueuedJob -> STM ()
enqueueJob RequestQueue {..} job = do
  case qjPriority job of
    High -> writeTQueue rqHigh job
    Normal -> writeTQueue rqNormal job
    Low -> writeTQueue rqLow job
  modifyTVar' rqSize (+ 1)

-- | Dequeue job (high priority first)
dequeueJob :: RequestQueue -> STM QueuedJob
dequeueJob RequestQueue {..} = do
  job <- readTQueue rqHigh
    `orElse` readTQueue rqNormal
    `orElse` readTQueue rqLow
  modifyTVar' rqSize (\n -> max 0 (n - 1))
  pure job

-- | Get queue size
queueSize :: RequestQueue -> STM Int32
queueSize RequestQueue {..} = readTVar rqSize

-- | Check if queue is empty
isEmpty :: RequestQueue -> STM Bool
isEmpty RequestQueue {..} = do
  highEmpty <- isEmptyTQueue rqHigh
  normalEmpty <- isEmptyTQueue rqNormal
  lowEmpty <- isEmptyTQueue rqLow
  pure (highEmpty && normalEmpty && lowEmpty)
