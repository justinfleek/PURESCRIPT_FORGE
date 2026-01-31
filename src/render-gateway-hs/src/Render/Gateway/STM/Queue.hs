{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Render Gateway STM Priority Queue
-- | Three-lane priority queue with O(1) operations
module Render.Gateway.STM.Queue where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Data.Int (Int32)
import Data.Text (Text)
import Data.Time (UTCTime)
import Data.Aeson (Value)

-- | Modality type (video or image)
data Modality = Video | Image
  deriving (Eq, Ord, Show)

-- | Task type per OpenAPI spec
data TaskType = T2V | I2V | T2I | I2I | Edit
  deriving (Eq, Ord, Show)

-- | Priority level
data Priority = High | Normal | Low
  deriving (Eq, Ord, Show)

-- | Job status
data JobStatus = Queued | Running | Complete | Error | Cancelled
  deriving (Eq, Ord, Show)

-- | Queued job with full request context
data QueuedJob = QueuedJob
  { qjJobId :: Text           -- Job ID (j_xxx format)
  , qjRequestId :: Text       -- Request ID for tracing
  , qjCustomerId :: Text      -- Customer ID from JWT
  , qjModality :: Modality    -- video or image
  , qjModelFamily :: Text     -- flux, wan, qwen, sdxl, zimage
  , qjModelName :: Text       -- flux-dev, wan-2.1, etc.
  , qjTask :: TaskType        -- t2v, i2v, t2i, i2i, edit
  , qjFormat :: Maybe Text    -- 720p, 1024, etc.
  , qjBackend :: Maybe Text   -- nunchaku, torch, tensorrt
  , qjPriority :: Priority
  , qjStatus :: JobStatus
  , qjCreatedAt :: UTCTime
  , qjStartedAt :: Maybe UTCTime
  , qjCompletedAt :: Maybe UTCTime
  , qjRequest :: Value        -- Full JSON request body
  , qjOutput :: Maybe Text    -- Output URL when complete
  , qjError :: Maybe Text     -- Error message if failed
  }

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

-- | Try to dequeue without blocking
tryDequeueJob :: RequestQueue -> STM (Maybe QueuedJob)
tryDequeueJob RequestQueue {..} = do
  mHigh <- tryReadTQueue rqHigh
  case mHigh of
    Just job -> do
      modifyTVar' rqSize (\n -> max 0 (n - 1))
      pure (Just job)
    Nothing -> do
      mNormal <- tryReadTQueue rqNormal
      case mNormal of
        Just job -> do
          modifyTVar' rqSize (\n -> max 0 (n - 1))
          pure (Just job)
        Nothing -> do
          mLow <- tryReadTQueue rqLow
          case mLow of
            Just job -> do
              modifyTVar' rqSize (\n -> max 0 (n - 1))
              pure (Just job)
            Nothing -> pure Nothing

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

-- | Parse task type from text
parseTaskType :: Text -> Maybe TaskType
parseTaskType "t2v" = Just T2V
parseTaskType "i2v" = Just I2V
parseTaskType "t2i" = Just T2I
parseTaskType "i2i" = Just I2I
parseTaskType "edit" = Just Edit
parseTaskType _ = Nothing

-- | Parse modality from text
parseModality :: Text -> Maybe Modality
parseModality "video" = Just Video
parseModality "image" = Just Image
parseModality _ = Nothing

-- | Parse priority from text
parsePriority :: Text -> Priority
parsePriority "high" = High
parsePriority "low" = Low
parsePriority _ = Normal
