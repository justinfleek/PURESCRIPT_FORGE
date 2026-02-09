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
module Forge.Render.Types
  ( -- * Re-exports from Modalities
    module Forge.Render.Types.Modalities
    -- * Re-exports from Tasks
  , module Forge.Render.Types.Tasks
    -- * Re-exports from Models
  , module Forge.Render.Types.Models
    -- * Re-exports from Formats
  , module Forge.Render.Types.Formats
    -- * Re-exports from Requests
  , module Forge.Render.Types.Requests
  ) where

-- Modalities and Families
import Forge.Render.Types.Modalities
  ( Modality(..)
  , allModalities
  , Family(..)
  , allFamilies
  , familyModality
  )

-- Tasks
import Forge.Render.Types.Tasks
  ( Task(..)
  , allTasks
  , TaskRequirements
  , taskRequirements
  )

-- Models
import Forge.Render.Types.Models
  ( Model(..)
  , allModels
  , ModelInfo
  , ModelStatus(..)
  , modelInfo
  )

-- Formats, Backends, Samplers
import Forge.Render.Types.Formats
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
import Forge.Render.Types.Requests
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
