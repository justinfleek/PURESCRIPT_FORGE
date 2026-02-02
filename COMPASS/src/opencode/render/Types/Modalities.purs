-- | Render Modalities and Families
-- |
-- | Output modalities and model family definitions.
-- |
-- | Coeffect Equation:
-- |   Modality : {Image, Video, 3D, Text, Code, Embedding}
-- |   Family : Modality -> BackboneArchitecture
-- |
-- | Module Coverage: Modality types, Family types, family-modality mapping
module Render.Types.Modalities
  ( -- * Modalities
    Modality(..)
  , allModalities
    -- * Families
  , Family(..)
  , allFamilies
  , familyModality
  ) where

import Prelude
import Data.Generic.Rep (class Generic)

--------------------------------------------------------------------------------
-- | Modalities
--------------------------------------------------------------------------------

-- | Output modality - what kind of content is produced
data Modality
  = Image       -- Static images
  | Video       -- Video sequences
  | ThreeD      -- 3D models/meshes
  | Text        -- LLM text output
  | Code        -- Code generation
  | Embedding   -- Vector embeddings

derive instance eqModality :: Eq Modality
derive instance ordModality :: Ord Modality
derive instance genericModality :: Generic Modality _

instance showModality :: Show Modality where
  show = case _ of
    Image -> "image"
    Video -> "video"
    ThreeD -> "3d"
    Text -> "text"
    Code -> "code"
    Embedding -> "embedding"

allModalities :: Array Modality
allModalities = [Image, Video, ThreeD, Text, Code, Embedding]

--------------------------------------------------------------------------------
-- | Model Families
--------------------------------------------------------------------------------

-- | Model family - distinct transformer backbones
data Family
  -- Image families
  = Flux          -- Black Forest Labs FLUX.1/2
  | ZImage        -- Alibaba Tongyi Z-Image
  | QwenImage     -- Alibaba Qwen-Image series
  | SDXL          -- Stability AI SDXL
  -- Video families
  | Wan           -- Alibaba WAN video
  | LTX           -- Lightricks LTX video
  | Hunyuan       -- Tencent Hunyuan video
  | SeedVR        -- ByteDance SeedVR upscaler
  -- 3D families
  | Trellis       -- Microsoft TRELLIS
  | Hunyuan3D     -- Tencent Hunyuan3D
  -- LLM families
  | Qwen          -- Alibaba Qwen LLM
  | DeepSeek      -- DeepSeek LLM
  | GLM           -- Zhipu GLM
  | Kimi          -- Moonshot Kimi
  -- Vision families
  | QwenVL        -- Qwen Vision-Language

derive instance eqFamily :: Eq Family
derive instance ordFamily :: Ord Family
derive instance genericFamily :: Generic Family _

instance showFamily :: Show Family where
  show = case _ of
    Flux -> "flux"
    ZImage -> "zimage"
    QwenImage -> "qwen-image"
    SDXL -> "sdxl"
    Wan -> "wan"
    LTX -> "ltx"
    Hunyuan -> "hunyuan"
    SeedVR -> "seedvr"
    Trellis -> "trellis"
    Hunyuan3D -> "hunyuan3d"
    Qwen -> "qwen"
    DeepSeek -> "deepseek"
    GLM -> "glm"
    Kimi -> "kimi"
    QwenVL -> "qwen-vl"

allFamilies :: Array Family
allFamilies = [Flux, ZImage, QwenImage, SDXL, Wan, LTX, Hunyuan, SeedVR, Trellis, Hunyuan3D, Qwen, DeepSeek, GLM, Kimi, QwenVL]

-- | Get primary modality for a family
familyModality :: Family -> Modality
familyModality = case _ of
  Flux -> Image
  ZImage -> Image
  QwenImage -> Image
  SDXL -> Image
  Wan -> Video
  LTX -> Video
  Hunyuan -> Video
  SeedVR -> Video
  Trellis -> ThreeD
  Hunyuan3D -> ThreeD
  Qwen -> Text
  DeepSeek -> Text
  GLM -> Code
  Kimi -> Text
  QwenVL -> Text
