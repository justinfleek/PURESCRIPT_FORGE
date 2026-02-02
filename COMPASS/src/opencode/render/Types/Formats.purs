-- | Render Formats and Backends
-- |
-- | Output formats, inference backends, and sampling configuration.
-- |
-- | Coeffect Equation:
-- |   Backend : Precision -> HardwareTarget
-- |   Format : Modality -> Resolution
-- |   Sampler * Scheduler : NoiseSchedule -> Denoising
-- |
-- | Module Coverage: Backend, VideoFormat, ImageFormat, Format, Sampler, Scheduler, NoiseType
module Render.Types.Formats
  ( -- * Backends
    Backend(..)
  , allBackends
    -- * Video Formats
  , VideoFormat(..)
    -- * Image Formats
  , ImageFormat(..)
    -- * Combined Format
  , Format(..)
    -- * Samplers
  , Sampler(..)
    -- * Schedulers
  , Scheduler(..)
    -- * Noise Types
  , NoiseType(..)
  ) where

import Prelude
import Data.Generic.Rep (class Generic)

--------------------------------------------------------------------------------
-- | Backends
--------------------------------------------------------------------------------

-- | Inference backends
data Backend
  = Nunchaku    -- NVFP4 on Blackwell, fastest
  | Torch       -- diffusers + CUDA, flexible
  | TensorRT    -- TRT-LLM + ModelOpt, production

derive instance eqBackend :: Eq Backend
derive instance ordBackend :: Ord Backend
derive instance genericBackend :: Generic Backend _

instance showBackend :: Show Backend where
  show = case _ of
    Nunchaku -> "nunchaku"
    Torch -> "torch"
    TensorRT -> "tensorrt"

allBackends :: Array Backend
allBackends = [Nunchaku, Torch, TensorRT]

--------------------------------------------------------------------------------
-- | Video Formats
--------------------------------------------------------------------------------

-- | Video output formats
data VideoFormat
  = V720p          -- 1280x720, 16:9
  | V720pPortrait  -- 720x1280, 9:16
  | V480p          -- 832x480, ~16:9
  | V480pPortrait  -- 480x832, ~9:16
  | VSquare        -- 640x640, 1:1
  | V1080p         -- 1920x1080, 16:9
  | V4K            -- 3840x2160, 16:9

derive instance eqVideoFormat :: Eq VideoFormat
derive instance genericVideoFormat :: Generic VideoFormat _

instance showVideoFormat :: Show VideoFormat where
  show = case _ of
    V720p -> "720p"
    V720pPortrait -> "720p-portrait"
    V480p -> "480p"
    V480pPortrait -> "480p-portrait"
    VSquare -> "square"
    V1080p -> "1080p"
    V4K -> "4k"

--------------------------------------------------------------------------------
-- | Image Formats
--------------------------------------------------------------------------------

-- | Image output formats
data ImageFormat
  = I1024          -- 1024x1024, 1:1
  | I512           -- 512x512, 1:1
  | IPortrait      -- 768x1024, 3:4
  | IPortraitWide  -- 576x1024, 9:16
  | ILandscape     -- 1024x768, 4:3
  | ILandscapeWide -- 1024x576, 16:9

derive instance eqImageFormat :: Eq ImageFormat
derive instance genericImageFormat :: Generic ImageFormat _

instance showImageFormat :: Show ImageFormat where
  show = case _ of
    I1024 -> "1024"
    I512 -> "512"
    IPortrait -> "portrait"
    IPortraitWide -> "portrait-wide"
    ILandscape -> "landscape"
    ILandscapeWide -> "landscape-wide"

--------------------------------------------------------------------------------
-- | Combined Format
--------------------------------------------------------------------------------

-- | Combined format type
data Format
  = VideoFmt VideoFormat
  | ImageFmt ImageFormat
  | ThreeDFmt String  -- glb, obj, etc.

derive instance eqFormat :: Eq Format
derive instance genericFormat :: Generic Format _

instance showFormat :: Show Format where
  show = case _ of
    VideoFmt v -> show v
    ImageFmt i -> show i
    ThreeDFmt s -> s

--------------------------------------------------------------------------------
-- | Samplers
--------------------------------------------------------------------------------

data Sampler
  = Euler        -- fast, good
  | Res2M        -- RES4LYF multistep
  | Res3S        -- RES4LYF substep, superior
  | Res2MSDE     -- SDE variant, organic
  | UniPC        -- fast, avoid on z-image

derive instance eqSampler :: Eq Sampler
derive instance genericSampler :: Generic Sampler _

instance showSampler :: Show Sampler where
  show = case _ of
    Euler -> "euler"
    Res2M -> "res_2m"
    Res3S -> "res_3s"
    Res2MSDE -> "res_2m_sde"
    UniPC -> "uni_pc"

--------------------------------------------------------------------------------
-- | Schedulers
--------------------------------------------------------------------------------

data Scheduler
  = Simple
  | Beta
  | Exponential
  | Karras
  | BongTangent   -- bidirectional, best for WAN/FLUX
  | Beta57        -- modified beta (a=0.5, b=0.7)

derive instance eqScheduler :: Eq Scheduler
derive instance genericScheduler :: Generic Scheduler _

instance showScheduler :: Show Scheduler where
  show = case _ of
    Simple -> "simple"
    Beta -> "beta"
    Exponential -> "exponential"
    Karras -> "karras"
    BongTangent -> "bong_tangent"
    Beta57 -> "beta57"

--------------------------------------------------------------------------------
-- | Noise Types
--------------------------------------------------------------------------------

data NoiseType
  = Gaussian   -- general use
  | Perlin     -- organic, photography
  | Brownian   -- natural textures
  | Fractal    -- creative variations

derive instance eqNoiseType :: Eq NoiseType
derive instance genericNoiseType :: Generic NoiseType _

instance showNoiseType :: Show NoiseType where
  show = case _ of
    Gaussian -> "gaussian"
    Perlin -> "perlin"
    Brownian -> "brownian"
    Fractal -> "fractal"
