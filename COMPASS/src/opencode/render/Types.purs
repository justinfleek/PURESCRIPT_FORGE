-- | Render API Types
-- |
-- | Generated from render.openapi.yaml with extensions for:
-- | - v2v (video-to-video) via LTX2
-- | - 3D generation via Trellis, Hunyuan3D
-- | - Coding models via GLM, Qwen, DeepSeek
-- | - Vision models via Qwen3-VL
-- |
-- | URL anatomy: /{modality}/{family}/{model}/{task}?format=...&backend=...
-- |
-- | Coeffect Equation:
-- |   RenderTypes : Modality * Family * Model * Task * Format -> Request -> Response
-- |   with resource flow: GPU^n -o Generation^1
-- |
-- | Module Structure:
-- |   Types.Modalities - Modality and Family definitions
-- |   Types.Tasks      - Task definitions and requirements
-- |   Types.Models     - Model variants and metadata
-- |   Types.Formats    - Backend, formats, samplers, schedulers
-- |   Types.Requests   - Request/response types, WebSocket
module Render.Types
  ( -- * Re-exports from Modalities
    module Render.Types.Modalities
    -- * Re-exports from Tasks
  , module Render.Types.Tasks
    -- * Re-exports from Models
  , module Render.Types.Models
    -- * Re-exports from Formats
  , module Render.Types.Formats
    -- * Re-exports from Requests
  , module Render.Types.Requests
  ) where

-- Modalities and Families
import Render.Types.Modalities
  ( Modality(..)
  , allModalities
  , Family(..)
  , allFamilies
  , familyModality
  )

-- Tasks
import Render.Types.Tasks
  ( Task(..)
  , allTasks
  , TaskRequirements
  , taskRequirements
  )

-- Models
import Render.Types.Models
  ( Model(..)
  , allModels
  , ModelInfo
  , ModelStatus(..)
  , modelInfo
  )

-- Formats, Backends, Samplers
import Render.Types.Formats
  ( Backend(..)
  , allBackends
  , VideoFormat(..)
  , ImageFormat(..)
  , Format(..)
  , Sampler(..)
  , Scheduler(..)
  , NoiseType(..)
  )

-- Requests and Responses
import Render.Types.Requests
  ( GenerationRequest
  , SyncRequest
  , AsyncRequest
  , SyncResponse
  , AsyncResponse
  , JobStatus(..)
  , Job
  , WSMessage(..)
  , WSFrame
  )
