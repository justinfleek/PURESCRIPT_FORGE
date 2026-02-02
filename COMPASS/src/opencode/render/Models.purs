-- | Render Model Registry
-- |
-- | Complete catalog of supported models with HuggingFace mappings,
-- | capabilities, and recommended configurations.
-- |
-- | Updated: 2026-02-01
module Render.Models
  ( -- Registry
    ModelRegistry
  , defaultRegistry
  , lookupModel
  , lookupByHF
  , modelsByFamily
  , modelsByModality
  , modelsByTask
    -- Model cards
  , ModelCard(..)
  , allModelCards
    -- Aliases
  , resolveAlias
  ) where

import Prelude

import Data.Array as Array
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

import Render.Types

-- ════════════════════════════════════════════════════════════════════════════
-- MODEL CARDS
-- ════════════════════════════════════════════════════════════════════════════

-- | Complete model card with all metadata
type ModelCard =
  { model :: Model
  , family :: Family
  , modality :: Modality
  , hfRepo :: String
  , hfUrl :: String
  , params :: String
  , tasks :: Array Task
  , defaultBackend :: Backend
  , status :: ModelStatus
  , quantizations :: Array String
  , recommendedGuidance :: { min :: Number, max :: Number }
  , recommendedSteps :: { min :: Int, max :: Int }
  , notes :: String
  }

-- | All registered model cards
allModelCards :: Array ModelCard
allModelCards =
  -- ══════════════════════════════════════════════════════════════════════════
  -- IMAGE MODELS
  -- ══════════════════════════════════════════════════════════════════════════
  
  -- FLUX family (Black Forest Labs)
  [ { model: FluxDev2
    , family: Flux
    , modality: Image
    , hfRepo: "black-forest-labs/FLUX.2-dev"
    , hfUrl: "https://huggingface.co/black-forest-labs/FLUX.2-dev/tree/main"
    , params: "32B"
    , tasks: [T2I, I2I]
    , defaultBackend: Nunchaku
    , status: Active
    , quantizations: ["bf16", "fp8", "nvfp4"]
    , recommendedGuidance: { min: 1.0, max: 4.0 }
    , recommendedSteps: { min: 20, max: 50 }
    , notes: "FLUX.2 Dev — Mistral-3 24B text encoder, highest quality"
    }
  , { model: FluxDev
    , family: Flux
    , modality: Image
    , hfRepo: "black-forest-labs/FLUX.1-dev"
    , hfUrl: "https://huggingface.co/black-forest-labs/FLUX.1-dev/tree/main"
    , params: "12B"
    , tasks: [T2I, I2I]
    , defaultBackend: Nunchaku
    , status: Active
    , quantizations: ["bf16", "fp8", "nvfp4"]
    , recommendedGuidance: { min: 1.0, max: 4.0 }
    , recommendedSteps: { min: 20, max: 50 }
    , notes: "FLUX.1 Dev — T5-XXL encoder"
    }
  , { model: FluxSchnell
    , family: Flux
    , modality: Image
    , hfRepo: "black-forest-labs/FLUX.1-schnell"
    , hfUrl: "https://huggingface.co/black-forest-labs/FLUX.1-schnell/tree/main"
    , params: "12B"
    , tasks: [T2I, I2I]
    , defaultBackend: Nunchaku
    , status: Active
    , quantizations: ["bf16", "fp8", "nvfp4"]
    , recommendedGuidance: { min: 3.5, max: 3.5 }
    , recommendedSteps: { min: 4, max: 4 }
    , notes: "FLUX.1 Schnell — 4 steps, fastest"
    }
  , { model: FluxKlein
    , family: Flux
    , modality: Image
    , hfRepo: "black-forest-labs/FLUX.2-klein-9B"
    , hfUrl: "https://huggingface.co/black-forest-labs/FLUX.2-klein-9B/tree/main"
    , params: "9B"
    , tasks: [T2I, I2I]
    , defaultBackend: Nunchaku
    , status: Active
    , quantizations: ["bf16", "fp8", "nvfp4"]
    , recommendedGuidance: { min: 2.0, max: 4.0 }
    , recommendedSteps: { min: 15, max: 30 }
    , notes: "FLUX.2 klein — efficient 9B variant"
    }
  
  -- Z-Image (Alibaba Tongyi)
  , { model: ZImageTurbo
    , family: ZImage
    , modality: Image
    , hfRepo: "Tongyi-MAI/Z-Image"
    , hfUrl: "https://huggingface.co/Tongyi-MAI/Z-Image/tree/main"
    , params: "6B"
    , tasks: [T2I]
    , defaultBackend: Nunchaku
    , status: Active
    , quantizations: ["bf16", "nvfp4"]
    , recommendedGuidance: { min: 1.0, max: 1.0 }
    , recommendedSteps: { min: 4, max: 8 }
    , notes: "Z-Image Turbo — sub-second generation, Apache-2.0"
    }
  
  -- Qwen-Image (Alibaba)
  , { model: QwenImage2512
    , family: QwenImage
    , modality: Image
    , hfRepo: "Qwen/Qwen-Image-2512"
    , hfUrl: "https://huggingface.co/Qwen/Qwen-Image-2512/tree/main"
    , params: "12B"
    , tasks: [T2I, I2I]
    , defaultBackend: Nunchaku
    , status: Active
    , quantizations: ["bf16", "fp8"]
    , recommendedGuidance: { min: 3.0, max: 7.0 }
    , recommendedSteps: { min: 20, max: 50 }
    , notes: "Qwen-Image-2512 — high resolution generation"
    }
  , { model: QwenImageLayered
    , family: QwenImage
    , modality: Image
    , hfRepo: "Qwen/Qwen-Image-Layered"
    , hfUrl: "https://huggingface.co/Qwen/Qwen-Image-Layered/tree/main"
    , params: "12B"
    , tasks: [I2I, Edit]
    , defaultBackend: Nunchaku
    , status: Active
    , quantizations: ["bf16", "fp8"]
    , recommendedGuidance: { min: 3.0, max: 7.0 }
    , recommendedSteps: { min: 20, max: 50 }
    , notes: "Qwen-Image-Layered — multi-layer editing, compositing"
    }
  , { model: QwenImageEdit
    , family: QwenImage
    , modality: Image
    , hfRepo: "Qwen/Qwen-Image-Edit-2511"
    , hfUrl: "https://huggingface.co/Qwen/Qwen-Image-Edit-2511/tree/main"
    , params: "12B"
    , tasks: [I2I, Edit]
    , defaultBackend: Nunchaku
    , status: Active
    , quantizations: ["bf16", "fp8"]
    , recommendedGuidance: { min: 3.0, max: 7.0 }
    , recommendedSteps: { min: 20, max: 50 }
    , notes: "Qwen-Image-Edit-2511 — superior multi-image editing"
    }

  -- ══════════════════════════════════════════════════════════════════════════
  -- VIDEO MODELS
  -- ══════════════════════════════════════════════════════════════════════════
  
  -- LTX (Lightricks)
  , { model: LTX2Default
    , family: LTX
    , modality: Video
    , hfRepo: "Lightricks/LTX-2"
    , hfUrl: "https://huggingface.co/Lightricks/LTX-2/tree/main"
    , params: "19B"
    , tasks: [T2V, I2V, V2V]
    , defaultBackend: Torch
    , status: Active
    , quantizations: ["bf16", "fp8"]
    , recommendedGuidance: { min: 3.0, max: 7.0 }
    , recommendedSteps: { min: 30, max: 50 }
    , notes: "LTX-2 19B — supports v2v (video-to-video)"
    }
  
  -- WAN (Alibaba)
  , { model: WanDefault
    , family: Wan
    , modality: Video
    , hfRepo: "Wan-AI/Wan2.2-I2V-A14B"
    , hfUrl: "https://huggingface.co/Wan-AI/Wan2.2-I2V-A14B/tree/main"
    , params: "14B×2 MoE"
    , tasks: [T2V, I2V]
    , defaultBackend: Torch
    , status: Active
    , quantizations: ["bf16", "nvfp4"]
    , recommendedGuidance: { min: 3.0, max: 7.0 }
    , recommendedSteps: { min: 30, max: 50 }
    , notes: "WAN 2.2 MoE — 14B×2 experts, NVFP4"
    }
  , { model: WanMove
    , family: Wan
    , modality: Video
    , hfRepo: "Ruihang/Wan-Move-14B-480P"
    , hfUrl: "https://huggingface.co/Ruihang/Wan-Move-14B-480P/tree/main"
    , params: "14B"
    , tasks: [I2V]
    , defaultBackend: Torch
    , status: Active
    , quantizations: ["bf16"]
    , recommendedGuidance: { min: 3.0, max: 7.0 }
    , recommendedSteps: { min: 30, max: 50 }
    , notes: "Wan-Move-14B — motion-focused i2v"
    }
  , { model: Wan22I2V
    , family: Wan
    , modality: Video
    , hfRepo: "Wan-AI/Wan2.2-I2V-A14B"
    , hfUrl: "https://huggingface.co/Wan-AI/Wan2.2-I2V-A14B/tree/main"
    , params: "14B"
    , tasks: [I2V]
    , defaultBackend: Torch
    , status: Active
    , quantizations: ["bf16", "nvfp4"]
    , recommendedGuidance: { min: 3.0, max: 7.0 }
    , recommendedSteps: { min: 30, max: 50 }
    , notes: "Wan2.2-I2V-A14B — latest i2v variant"
    }
  
  -- Hunyuan Video (Tencent)
  , { model: HunyuanVideo15
    , family: Hunyuan
    , modality: Video
    , hfRepo: "tencent/HunyuanVideo-1.5"
    , hfUrl: "https://huggingface.co/tencent/HunyuanVideo-1.5/tree/main"
    , params: "13B"
    , tasks: [T2V, I2V]
    , defaultBackend: Torch
    , status: Active
    , quantizations: ["bf16", "fp8"]
    , recommendedGuidance: { min: 5.0, max: 10.0 }
    , recommendedSteps: { min: 40, max: 80 }
    , notes: "HunyuanVideo-1.5 — high quality, longer videos"
    }
  
  -- SeedVR (ByteDance)
  , { model: SeedVR2
    , family: SeedVR
    , modality: Video
    , hfRepo: "ByteDance-Seed/SeedVR2-7B"
    , hfUrl: "https://huggingface.co/ByteDance-Seed/SeedVR2-7B/tree/main"
    , params: "7B"
    , tasks: [VideoUpscale]
    , defaultBackend: Torch
    , status: Active
    , quantizations: ["bf16"]
    , recommendedGuidance: { min: 1.0, max: 3.0 }
    , recommendedSteps: { min: 10, max: 20 }
    , notes: "SeedVR2-7B — video upscaling and enhancement"
    }

  -- ══════════════════════════════════════════════════════════════════════════
  -- 3D MODELS
  -- ══════════════════════════════════════════════════════════════════════════
  
  -- Trellis (Microsoft)
  , { model: Trellis2
    , family: Trellis
    , modality: ThreeD
    , hfRepo: "microsoft/TRELLIS.2-4B"
    , hfUrl: "https://huggingface.co/microsoft/TRELLIS.2-4B/tree/main"
    , params: "4B"
    , tasks: [I23D, T23D]
    , defaultBackend: Torch
    , status: Active
    , quantizations: ["bf16"]
    , recommendedGuidance: { min: 5.0, max: 10.0 }
    , recommendedSteps: { min: 50, max: 100 }
    , notes: "TRELLIS.2-4B — image/text to 3D mesh"
    }
  
  -- Hunyuan3D (Tencent)
  , { model: Hunyuan3D21
    , family: Hunyuan3D
    , modality: ThreeD
    , hfRepo: "tencent/Hunyuan3D-2.1"
    , hfUrl: "https://huggingface.co/tencent/Hunyuan3D-2.1/tree/main"
    , params: "7B"
    , tasks: [I23D, T23D]
    , defaultBackend: Torch
    , status: Active
    , quantizations: ["bf16", "fp8"]
    , recommendedGuidance: { min: 5.0, max: 15.0 }
    , recommendedSteps: { min: 50, max: 150 }
    , notes: "Hunyuan3D-2.1 — high-quality 3D generation"
    }

  -- ══════════════════════════════════════════════════════════════════════════
  -- LLM / CODING MODELS
  -- ══════════════════════════════════════════════════════════════════════════
  
  -- Qwen (Alibaba)
  , { model: Qwen3Instruct
    , family: Qwen
    , modality: Text
    , hfRepo: "Qwen/Qwen3-235B-A22B-Instruct-2507"
    , hfUrl: "https://huggingface.co/Qwen/Qwen3-235B-A22B-Instruct-2507"
    , params: "235B (22B active)"
    , tasks: [Completion, Chat]
    , defaultBackend: TensorRT
    , status: Active
    , quantizations: ["bf16", "fp8", "int8", "int4"]
    , recommendedGuidance: { min: 0.0, max: 0.0 }
    , recommendedSteps: { min: 0, max: 0 }
    , notes: "Qwen3-235B-A22B-Instruct — flagship MoE LLM"
    }
  , { model: Qwen3Coder
    , family: Qwen
    , modality: Code
    , hfRepo: "Qwen/Qwen3-Coder-480B-A35B-Instruct"
    , hfUrl: "https://huggingface.co/Qwen/Qwen3-Coder-480B-A35B-Instruct/tree/main"
    , params: "480B (35B active)"
    , tasks: [Completion, Chat]
    , defaultBackend: TensorRT
    , status: Active
    , quantizations: ["bf16", "fp8", "int8"]
    , recommendedGuidance: { min: 0.0, max: 0.0 }
    , recommendedSteps: { min: 0, max: 0 }
    , notes: "Qwen3-Coder-480B — largest coding model"
    }
  
  -- DeepSeek
  , { model: DeepSeekV32
    , family: DeepSeek
    , modality: Text
    , hfRepo: "deepseek-ai/DeepSeek-V3.2"
    , hfUrl: "https://huggingface.co/deepseek-ai/DeepSeek-V3.2/tree/main"
    , params: "671B"
    , tasks: [Completion, Chat]
    , defaultBackend: TensorRT
    , status: Active
    , quantizations: ["bf16", "fp8", "int8"]
    , recommendedGuidance: { min: 0.0, max: 0.0 }
    , recommendedSteps: { min: 0, max: 0 }
    , notes: "DeepSeek-V3.2 — 671B, strong reasoning"
    }
  
  -- GLM (Zhipu)
  , { model: GLM47Coding
    , family: GLM
    , modality: Code
    , hfRepo: "zai-org/GLM-4.7"
    , hfUrl: "https://huggingface.co/zai-org/GLM-4.7/tree/main"
    , params: "9B"
    , tasks: [Completion, Chat]
    , defaultBackend: TensorRT
    , status: Active
    , quantizations: ["bf16", "fp8", "int4"]
    , recommendedGuidance: { min: 0.0, max: 0.0 }
    , recommendedSteps: { min: 0, max: 0 }
    , notes: "GLM-4.7 Coding — optimized for code"
    }
  , { model: GLM47Flash
    , family: GLM
    , modality: Text
    , hfRepo: "zai-org/GLM-4.7-Flash"
    , hfUrl: "https://huggingface.co/zai-org/GLM-4.7-Flash/tree/main"
    , params: "9B"
    , tasks: [Completion, Chat]
    , defaultBackend: TensorRT
    , status: Active
    , quantizations: ["bf16", "fp8", "int4"]
    , recommendedGuidance: { min: 0.0, max: 0.0 }
    , recommendedSteps: { min: 0, max: 0 }
    , notes: "GLM-4.7-Flash — fast inference variant"
    }
  
  -- Kimi (Moonshot)
  , { model: KimiK25
    , family: Kimi
    , modality: Text
    , hfRepo: "moonshotai/Kimi-K2.5"
    , hfUrl: "https://huggingface.co/moonshotai/Kimi-K2.5/tree/main"
    , params: "200B+"
    , tasks: [Completion, Chat]
    , defaultBackend: TensorRT
    , status: Active
    , quantizations: ["bf16", "fp8"]
    , recommendedGuidance: { min: 0.0, max: 0.0 }
    , recommendedSteps: { min: 0, max: 0 }
    , notes: "Kimi-K2.5 — long context, strong reasoning"
    }

  -- ══════════════════════════════════════════════════════════════════════════
  -- VISION MODELS
  -- ══════════════════════════════════════════════════════════════════════════
  
  -- Qwen-VL
  , { model: Qwen3VL8B
    , family: QwenVL
    , modality: Embedding
    , hfRepo: "Qwen/Qwen3-VL-Embedding-8B"
    , hfUrl: "https://huggingface.co/Qwen/Qwen3-VL-Embedding-8B/tree/main"
    , params: "8B"
    , tasks: [VQA, Caption, Embed]
    , defaultBackend: TensorRT
    , status: Active
    , quantizations: ["bf16", "fp8"]
    , recommendedGuidance: { min: 0.0, max: 0.0 }
    , recommendedSteps: { min: 0, max: 0 }
    , notes: "Qwen3-VL-Embedding-8B — vision-language embeddings"
    }
  ]

-- ════════════════════════════════════════════════════════════════════════════
-- REGISTRY
-- ════════════════════════════════════════════════════════════════════════════

type ModelRegistry = Map.Map Model ModelCard

defaultRegistry :: ModelRegistry
defaultRegistry = Map.fromFoldable $ map (\c -> Tuple c.model c) allModelCards

lookupModel :: Model -> ModelRegistry -> Maybe ModelCard
lookupModel = Map.lookup

-- | Lookup by HuggingFace repo name
lookupByHF :: String -> ModelRegistry -> Maybe ModelCard
lookupByHF repo registry = 
  Array.find (\c -> c.hfRepo == repo) (Map.values registry)

-- | Get all models for a family
modelsByFamily :: Family -> ModelRegistry -> Array ModelCard
modelsByFamily fam registry =
  Array.filter (\c -> c.family == fam) (Map.values registry)

-- | Get all models for a modality
modelsByModality :: Modality -> ModelRegistry -> Array ModelCard
modelsByModality mod registry =
  Array.filter (\c -> c.modality == mod) (Map.values registry)

-- | Get all models that support a task
modelsByTask :: Task -> ModelRegistry -> Array ModelCard
modelsByTask task registry =
  Array.filter (\c -> Array.elem task c.tasks) (Map.values registry)

-- ════════════════════════════════════════════════════════════════════════════
-- ALIASES
-- ════════════════════════════════════════════════════════════════════════════

-- | HuggingFace model ID aliases
type AliasMap = Map.Map String { family :: Family, model :: Model }

aliasMap :: AliasMap
aliasMap = Map.fromFoldable
  [ Tuple "black-forest-labs/FLUX.2-dev" { family: Flux, model: FluxDev2 }
  , Tuple "black-forest-labs/FLUX.1-dev" { family: Flux, model: FluxDev }
  , Tuple "black-forest-labs/FLUX.1-schnell" { family: Flux, model: FluxSchnell }
  , Tuple "black-forest-labs/FLUX.2-klein-9B" { family: Flux, model: FluxKlein }
  , Tuple "Tongyi-MAI/Z-Image" { family: ZImage, model: ZImageTurbo }
  , Tuple "Lightricks/LTX-2" { family: LTX, model: LTX2Default }
  , Tuple "microsoft/TRELLIS.2-4B" { family: Trellis, model: Trellis2 }
  , Tuple "tencent/Hunyuan3D-2.1" { family: Hunyuan3D, model: Hunyuan3D21 }
  , Tuple "Qwen/Qwen3-Coder-480B-A35B-Instruct" { family: Qwen, model: Qwen3Coder }
  , Tuple "deepseek-ai/DeepSeek-V3.2" { family: DeepSeek, model: DeepSeekV32 }
  , Tuple "moonshotai/Kimi-K2.5" { family: Kimi, model: KimiK25 }
  , Tuple "zai-org/GLM-4.7" { family: GLM, model: GLM47Coding }
  ]

-- | Resolve HuggingFace ID to family/model
resolveAlias :: String -> Maybe { family :: Family, model :: Model }
resolveAlias = flip Map.lookup aliasMap
