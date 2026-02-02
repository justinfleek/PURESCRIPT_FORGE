-- | Render Models
-- |
-- | Specific model variants and metadata.
-- |
-- | Coeffect Equation:
-- |   Model : Family -> Variant -> Parameters
-- |   ModelInfo : Model -> {repo, params, tasks, backend, status}
-- |
-- | Module Coverage: Model enum, ModelInfo, ModelStatus, model registry
module Render.Types.Models
  ( -- * Models
    Model(..)
  , allModels
    -- * Model Info
  , ModelInfo
  , ModelStatus(..)
  , modelInfo
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Render.Types.Modalities (Family(..))
import Render.Types.Tasks (Task(..))
import Render.Types.Formats (Backend(..))

--------------------------------------------------------------------------------
-- | Models
--------------------------------------------------------------------------------

-- | Specific model variants
data Model
  -- FLUX (Image)
  = FluxDev2         -- FLUX.2 Dev 32B, Mistral-3 24B encoder
  | FluxDev          -- FLUX.1 Dev 12B, T5-XXL encoder  
  | FluxSchnell      -- FLUX.1 Schnell 12B, 4 steps
  | FluxKlein        -- FLUX.2 klein 9B
  -- Z-Image (Image)
  | ZImageTurbo      -- Z-Image Turbo 6B, sub-second
  -- Qwen-Image (Image/Edit)
  | QwenImage2512    -- Qwen-Image-2512
  | QwenImageLayered -- Qwen-Image-Layered (multi-layer edit)
  | QwenImageEdit    -- Qwen-Image-Edit-2511
  -- WAN (Video)
  | WanDefault       -- WAN 2.2 MoE 14B×2, NVFP4
  | WanMove          -- Wan-Move-14B-480P
  | Wan22I2V         -- Wan2.2-I2V-A14B
  -- LTX (Video)
  | LTX2Default      -- LTX-2 19B
  -- Hunyuan (Video)
  | HunyuanVideo15   -- HunyuanVideo-1.5
  -- SeedVR (Video Upscale)
  | SeedVR2          -- SeedVR2-7B upscaler
  -- Trellis (3D)
  | Trellis2         -- TRELLIS.2-4B
  -- Hunyuan3D (3D)
  | Hunyuan3D21      -- Hunyuan3D-2.1
  -- Qwen LLM
  | Qwen3Instruct    -- Qwen3-235B-A22B-Instruct
  | Qwen3Coder       -- Qwen3-Coder-480B-A35B-Instruct
  -- DeepSeek
  | DeepSeekV32      -- DeepSeek-V3.2
  -- GLM (Coding)
  | GLM47Coding      -- GLM-4.7 Coding
  | GLM47Flash       -- GLM-4.7-Flash
  -- Kimi
  | KimiK25          -- Kimi-K2.5
  -- Qwen-VL (Vision)
  | Qwen3VL8B        -- Qwen3-VL-Embedding-8B

derive instance eqModel :: Eq Model
derive instance ordModel :: Ord Model
derive instance genericModel :: Generic Model _

instance showModel :: Show Model where
  show = case _ of
    FluxDev2 -> "dev2"
    FluxDev -> "dev"
    FluxSchnell -> "schnell"
    FluxKlein -> "klein"
    ZImageTurbo -> "turbo"
    QwenImage2512 -> "2512"
    QwenImageLayered -> "layered"
    QwenImageEdit -> "edit-2511"
    WanDefault -> "default"
    WanMove -> "move"
    Wan22I2V -> "2.2-i2v"
    LTX2Default -> "default"
    HunyuanVideo15 -> "1.5"
    SeedVR2 -> "2"
    Trellis2 -> "2"
    Hunyuan3D21 -> "2.1"
    Qwen3Instruct -> "235b-instruct"
    Qwen3Coder -> "coder-480b"
    DeepSeekV32 -> "v3.2"
    GLM47Coding -> "4.7-coding"
    GLM47Flash -> "4.7-flash"
    KimiK25 -> "k2.5"
    Qwen3VL8B -> "vl-8b"

allModels :: Array Model
allModels = 
  [ FluxDev2, FluxDev, FluxSchnell, FluxKlein
  , ZImageTurbo
  , QwenImage2512, QwenImageLayered, QwenImageEdit
  , WanDefault, WanMove, Wan22I2V
  , LTX2Default
  , HunyuanVideo15
  , SeedVR2
  , Trellis2
  , Hunyuan3D21
  , Qwen3Instruct, Qwen3Coder
  , DeepSeekV32
  , GLM47Coding, GLM47Flash
  , KimiK25
  , Qwen3VL8B
  ]

--------------------------------------------------------------------------------
-- | Model Status
--------------------------------------------------------------------------------

data ModelStatus = Active | ComingSoon | Beta | Deprecated

derive instance eqModelStatus :: Eq ModelStatus
derive instance genericModelStatus :: Generic ModelStatus _

instance showModelStatus :: Show ModelStatus where
  show = genericShow

--------------------------------------------------------------------------------
-- | Model Info
--------------------------------------------------------------------------------

-- | Model metadata
type ModelInfo =
  { model :: Model
  , family :: Family
  , hfRepo :: String           -- HuggingFace repo
  , params :: String           -- Parameter count
  , tasks :: Array Task        -- Supported tasks
  , defaultBackend :: Backend
  , status :: ModelStatus
  }

-- | Get model info
modelInfo :: Model -> ModelInfo
modelInfo = case _ of
  FluxDev2 ->
    { model: FluxDev2
    , family: Flux
    , hfRepo: "black-forest-labs/FLUX.2-dev"
    , params: "32B"
    , tasks: [T2I, I2I]
    , defaultBackend: Nunchaku
    , status: Active
    }
  FluxKlein ->
    { model: FluxKlein
    , family: Flux
    , hfRepo: "black-forest-labs/FLUX.2-klein-9B"
    , params: "9B"
    , tasks: [T2I, I2I]
    , defaultBackend: Nunchaku
    , status: Active
    }
  ZImageTurbo ->
    { model: ZImageTurbo
    , family: ZImage
    , hfRepo: "Tongyi-MAI/Z-Image"
    , params: "6B"
    , tasks: [T2I]
    , defaultBackend: Nunchaku
    , status: Active
    }
  LTX2Default ->
    { model: LTX2Default
    , family: LTX
    , hfRepo: "Lightricks/LTX-2"
    , params: "19B"
    , tasks: [T2V, I2V, V2V]
    , defaultBackend: Torch
    , status: Active
    }
  Trellis2 ->
    { model: Trellis2
    , family: Trellis
    , hfRepo: "microsoft/TRELLIS.2-4B"
    , params: "4B"
    , tasks: [I23D, T23D]
    , defaultBackend: Torch
    , status: Active
    }
  Hunyuan3D21 ->
    { model: Hunyuan3D21
    , family: Hunyuan3D
    , hfRepo: "tencent/Hunyuan3D-2.1"
    , params: "7B"
    , tasks: [I23D, T23D]
    , defaultBackend: Torch
    , status: Active
    }
  Qwen3Coder ->
    { model: Qwen3Coder
    , family: Qwen
    , hfRepo: "Qwen/Qwen3-Coder-480B-A35B-Instruct"
    , params: "480B (35B active)"
    , tasks: [Completion, Chat]
    , defaultBackend: TensorRT
    , status: Active
    }
  GLM47Coding ->
    { model: GLM47Coding
    , family: GLM
    , hfRepo: "zai-org/GLM-4.7"
    , params: "9B"
    , tasks: [Completion, Chat]
    , defaultBackend: TensorRT
    , status: Active
    }
  KimiK25 ->
    { model: KimiK25
    , family: Kimi
    , hfRepo: "moonshotai/Kimi-K2.5"
    , params: "200B+"
    , tasks: [Completion, Chat]
    , defaultBackend: TensorRT
    , status: Active
    }
  DeepSeekV32 ->
    { model: DeepSeekV32
    , family: DeepSeek
    , hfRepo: "deepseek-ai/DeepSeek-V3.2"
    , params: "671B"
    , tasks: [Completion, Chat]
    , defaultBackend: TensorRT
    , status: Active
    }
  -- Default case for others
  m ->
    { model: m
    , family: Flux
    , hfRepo: ""
    , params: ""
    , tasks: []
    , defaultBackend: Torch
    , status: ComingSoon
    }
