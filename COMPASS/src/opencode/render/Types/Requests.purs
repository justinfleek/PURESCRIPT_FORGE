-- | Render Requests and Responses
-- |
-- | API request/response types and WebSocket messages.
-- |
-- | Coeffect Equation:
-- |   Request : Family * Model * Task * Params -> Job
-- |   Response : Job -> Status * Result
-- |   WebSocket : Request -o Stream Progress
-- |
-- | Module Coverage: GenerationRequest, SyncRequest, AsyncRequest, responses, WebSocket
module Render.Types.Requests
  ( -- * Requests
    GenerationRequest
  , SyncRequest
  , AsyncRequest
    -- * Responses
  , SyncResponse
  , AsyncResponse
  , JobStatus(..)
  , Job
    -- * WebSocket
  , WSMessage(..)
  , WSFrame
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Render.Types.Modalities (Family)
import Render.Types.Tasks (Task)
import Render.Types.Models (Model)
import Render.Types.Formats (Backend, Format, Sampler, Scheduler, NoiseType)

--------------------------------------------------------------------------------
-- | Requests
--------------------------------------------------------------------------------

-- | Base generation parameters
type GenerationRequest =
  { prompt :: Maybe String
  , negativePrompt :: Maybe String
  , image :: Maybe String        -- URL or base64
  , video :: Maybe String        -- URL for v2v
  , mask :: Maybe String         -- URL or base64 for edit
  , format :: Format
  , steps :: Maybe Int
  , guidance :: Maybe Number
  , seed :: Maybe Int
  , sampler :: Maybe Sampler
  , scheduler :: Maybe Scheduler
  , noise :: Maybe NoiseType
  , eta :: Maybe Number          -- noise injection 0.0-1.0
  , backend :: Maybe Backend
  }

-- | Sync tier request (returns bytes directly)
type SyncRequest =
  { family :: Family
  , model :: Model
  , task :: Task
  , params :: GenerationRequest
  }

-- | Async tier request (returns job ID)
type AsyncRequest =
  { family :: Family
  , model :: Model
  , task :: Task
  , params :: GenerationRequest
  , webhook :: Maybe String      -- callback URL
  , priority :: Maybe Int        -- queue priority
  }

--------------------------------------------------------------------------------
-- | Responses
--------------------------------------------------------------------------------

-- | Sync response (200 = bytes, 503 = retry)
type SyncResponse =
  { contentType :: String
  , contentLength :: Int
  , contentLocation :: String    -- CDN URL
  , retryAfter :: Maybe Int      -- seconds if 503
  }

-- | Job status
data JobStatus
  = Queued
  | Processing
  | Complete
  | Failed
  | Cancelled

derive instance eqJobStatus :: Eq JobStatus
derive instance genericJobStatus :: Generic JobStatus _

instance showJobStatus :: Show JobStatus where
  show = genericShow

-- | Job record
type Job =
  { id :: String
  , status :: JobStatus
  , progress :: Maybe Number     -- 0.0-1.0
  , result :: Maybe String       -- CDN URL when complete
  , error :: Maybe String        -- error message if failed
  , created :: Number
  , updated :: Number
  }

-- | Async response
type AsyncResponse =
  { accepted :: Boolean          -- 202 = true
  , job :: Maybe Job
  , retryAfter :: Maybe Int      -- seconds if 429
  }

--------------------------------------------------------------------------------
-- | WebSocket
--------------------------------------------------------------------------------

-- | WebSocket message types
data WSMessage
  = WSSubmit AsyncRequest        -- submit job
  | WSSubscribe String           -- subscribe to job ID
  | WSUnsubscribe String         -- unsubscribe
  | WSProgress Job               -- progress update
  | WSFrame WSFrame              -- intermediate frame
  | WSComplete Job               -- job complete
  | WSError String               -- error message

derive instance genericWSMessage :: Generic WSMessage _

instance showWSMessage :: Show WSMessage where
  show = genericShow

-- | Intermediate frame for streaming
type WSFrame =
  { jobId :: String
  , frameIndex :: Int
  , totalFrames :: Int
  , data :: String               -- base64 encoded
  , timestamp :: Number
  }
