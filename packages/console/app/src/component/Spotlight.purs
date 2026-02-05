-- | Spotlight WebGPU Effect Component
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/component/spotlight.tsx
-- | Pure PureScript implementation - NO FFI
-- | 
-- | This module defines the configuration and state types for the WebGPU
-- | spotlight effect. The actual WebGPU rendering would require platform
-- | bindings, but all configuration and state management is pure.
module Console.App.Component.Spotlight
  ( SpotlightConfig
  , ParticlesConfig
  , SpotlightAnimationState
  , PulsatingConfig(..)
  , Placement
  , HexColor
  , RGB
  , UniformData
  , defaultConfig
  , defaultParticlesConfig
  , mkPlacement
  , mkHexColor
  , hexToRgb
  , getAnchorAndDir
  , buildUniformData
  , updateUniformData
  , uniformBufferSize
  ) where

import Prelude

import Data.Array (index)
import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (sqrt, sin, cos)
import Data.String (Pattern(..), split, length, drop, take)
import Data.String.CodeUnits (charAt)
import Data.Tuple (Tuple(..))

-- | Placement coordinates (normalized 0-1)
type Placement = Tuple Number Number

-- | Smart constructor for placement
mkPlacement :: Number -> Number -> Maybe Placement
mkPlacement x y
  | x >= -1.0 && x <= 2.0 && y >= -1.0 && y <= 2.0 = Just (Tuple x y)
  | otherwise = Nothing

-- | Hex color string
newtype HexColor = HexColor String

derive instance eqHexColor :: Eq HexColor
derive instance ordHexColor :: Ord HexColor

instance showHexColor :: Show HexColor where
  show (HexColor c) = "(HexColor " <> show c <> ")"

-- | Smart constructor for hex color
mkHexColor :: String -> Maybe HexColor
mkHexColor s
  | length s == 7 && take 1 s == "#" = Just (HexColor s)
  | length s == 6 = Just (HexColor ("#" <> s))
  | otherwise = Nothing

-- | RGB color tuple (0-1 range)
type RGB = { r :: Number, g :: Number, b :: Number }

-- | Parse hex digit to number
hexDigitToInt :: Char -> Maybe Int
hexDigitToInt c = case c of
  '0' -> Just 0
  '1' -> Just 1
  '2' -> Just 2
  '3' -> Just 3
  '4' -> Just 4
  '5' -> Just 5
  '6' -> Just 6
  '7' -> Just 7
  '8' -> Just 8
  '9' -> Just 9
  'a' -> Just 10
  'b' -> Just 11
  'c' -> Just 12
  'd' -> Just 13
  'e' -> Just 14
  'f' -> Just 15
  'A' -> Just 10
  'B' -> Just 11
  'C' -> Just 12
  'D' -> Just 13
  'E' -> Just 14
  'F' -> Just 15
  _ -> Nothing

-- | Parse two hex characters to int
parseHexPair :: String -> Int -> Maybe Int
parseHexPair s offset = do
  c1 <- charAt offset s
  c2 <- charAt (offset + 1) s
  h1 <- hexDigitToInt c1
  h2 <- hexDigitToInt c2
  pure (h1 * 16 + h2)

-- | Convert hex color to RGB (pure implementation)
hexToRgb :: HexColor -> RGB
hexToRgb (HexColor hex) =
  let
    cleanHex = if take 1 hex == "#" then drop 1 hex else hex
    r = fromMaybe 255 (parseHexPair cleanHex 0)
    g = fromMaybe 255 (parseHexPair cleanHex 2)
    b = fromMaybe 255 (parseHexPair cleanHex 4)
  in
    { r: toNumber r / 255.0
    , g: toNumber g / 255.0
    , b: toNumber b / 255.0
    }

-- | Pulsating range (false or min/max tuple)
data PulsatingConfig
  = NoPulsating
  | Pulsating { min :: Number, max :: Number }

derive instance eqPulsatingConfig :: Eq PulsatingConfig

instance showPulsatingConfig :: Show PulsatingConfig where
  show NoPulsating = "NoPulsating"
  show (Pulsating r) = "(Pulsating " <> show r.min <> " " <> show r.max <> ")"

-- | Particles configuration
type ParticlesConfig =
  { enabled :: Boolean
  , amount :: Int
  , sizeMin :: Number
  , sizeMax :: Number
  , speed :: Number
  , opacity :: Number
  , drift :: Number
  }

-- | Default particles config from source
defaultParticlesConfig :: ParticlesConfig
defaultParticlesConfig =
  { enabled: true
  , amount: 70
  , sizeMin: 1.25
  , sizeMax: 1.5
  , speed: 0.75
  , opacity: 0.9
  , drift: 1.5
  }

-- | Spotlight configuration
type SpotlightConfig =
  { placement :: Placement
  , color :: HexColor
  , speed :: Number
  , spread :: Number
  , length :: Number
  , width :: Number
  , pulsating :: PulsatingConfig
  , distance :: Number
  , saturation :: Number
  , noiseAmount :: Number
  , distortion :: Number
  , opacity :: Number
  , particles :: ParticlesConfig
  }

-- | Default spotlight config from source
defaultConfig :: SpotlightConfig
defaultConfig =
  { placement: Tuple 0.5 (-0.15)
  , color: HexColor "#ffffff"
  , speed: 0.8
  , spread: 0.5
  , length: 4.0
  , width: 0.15
  , pulsating: Pulsating { min: 0.95, max: 1.1 }
  , distance: 3.5
  , saturation: 0.35
  , noiseAmount: 0.15
  , distortion: 0.05
  , opacity: 0.325
  , particles: defaultParticlesConfig
  }

-- | Animation state
type SpotlightAnimationState =
  { time :: Number
  , intensity :: Number
  , pulseValue :: Number
  }

-- | Anchor and direction result
type AnchorDir =
  { anchor :: Tuple Number Number
  , dir :: Tuple Number Number
  }

-- | Calculate anchor point and direction based on placement (pure)
getAnchorAndDir :: Placement -> Number -> Number -> AnchorDir
getAnchorAndDir (Tuple px py) w h =
  let
    outside = 0.2
    centerX = 0.5
    centerY = 0.5
    
    -- Calculate initial values
    initialAnchorX = px * w
    initialAnchorY = py * h
    
    -- Determine anchor and direction based on placement
    result = 
      if py <= 0.25 then
        { anchorX: px * w
        , anchorY: (-outside) * h + py * h
        , dirX: (centerX - px) * 0.5
        , dirY: 1.0
        }
      else if py >= 0.75 then
        { anchorX: px * w
        , anchorY: (1.0 + outside) * h - (1.0 - py) * h
        , dirX: (centerX - px) * 0.5
        , dirY: -1.0
        }
      else if px <= 0.25 then
        { anchorX: (-outside) * w + px * w
        , anchorY: py * h
        , dirX: 1.0
        , dirY: (centerY - py) * 0.5
        }
      else if px >= 0.75 then
        { anchorX: (1.0 + outside) * w - (1.0 - px) * w
        , anchorY: py * h
        , dirX: -1.0
        , dirY: (centerY - py) * 0.5
        }
      else
        { anchorX: initialAnchorX
        , anchorY: initialAnchorY
        , dirX: 0.0
        , dirY: 1.0
        }
    
    -- Normalize direction
    len = sqrt (result.dirX * result.dirX + result.dirY * result.dirY)
    normDirX = if len > 0.0 then result.dirX / len else result.dirX
    normDirY = if len > 0.0 then result.dirY / len else result.dirY
  in
    { anchor: Tuple result.anchorX result.anchorY
    , dir: Tuple normDirX normDirY
    }

-- | Uniform buffer size (144 bytes as per source)
uniformBufferSize :: Int
uniformBufferSize = 144

-- | Uniform data structure for WebGPU shader
type UniformData =
  { iTime :: Number
  , iResolution :: Tuple Number Number
  , lightPos :: Tuple Number Number
  , lightDir :: Tuple Number Number
  , color :: RGB
  , speed :: Number
  , lightSpread :: Number
  , lightLength :: Number
  , sourceWidth :: Number
  , pulsating :: Number
  , pulsatingMin :: Number
  , pulsatingMax :: Number
  , fadeDistance :: Number
  , saturation :: Number
  , noiseAmount :: Number
  , distortion :: Number
  , particlesEnabled :: Number
  , particleAmount :: Number
  , particleSizeMin :: Number
  , particleSizeMax :: Number
  , particleSpeed :: Number
  , particleOpacity :: Number
  , particleDrift :: Number
  }

-- | Build uniform data from config (pure)
buildUniformData :: SpotlightConfig -> Number -> Number -> Number -> UniformData
buildUniformData config w h time =
  let
    anchorDir = getAnchorAndDir config.placement w h
    rgb = hexToRgb config.color
    pulsatingValue = case config.pulsating of
      NoPulsating -> 0.0
      Pulsating _ -> 1.0
    pulsatingMinValue = case config.pulsating of
      NoPulsating -> 1.0
      Pulsating r -> r.min
    pulsatingMaxValue = case config.pulsating of
      NoPulsating -> 1.0
      Pulsating r -> r.max
  in
    { iTime: time
    , iResolution: Tuple w h
    , lightPos: anchorDir.anchor
    , lightDir: anchorDir.dir
    , color: rgb
    , speed: config.speed
    , lightSpread: config.spread
    , lightLength: config.length
    , sourceWidth: config.width
    , pulsating: pulsatingValue
    , pulsatingMin: pulsatingMinValue
    , pulsatingMax: pulsatingMaxValue
    , fadeDistance: config.distance
    , saturation: config.saturation
    , noiseAmount: config.noiseAmount
    , distortion: config.distortion
    , particlesEnabled: if config.particles.enabled then 1.0 else 0.0
    , particleAmount: toNumber config.particles.amount
    , particleSizeMin: config.particles.sizeMin
    , particleSizeMax: config.particles.sizeMax
    , particleSpeed: config.particles.speed
    , particleOpacity: config.particles.opacity
    , particleDrift: config.particles.drift
    }

-- | Update uniform data with new time (pure)
updateUniformData :: UniformData -> Number -> UniformData
updateUniformData uniforms newTime = uniforms { iTime = newTime }

-- | Calculate animation state (pure)
calculateAnimationState :: SpotlightConfig -> Number -> SpotlightAnimationState
calculateAnimationState config time =
  let
    pulsatingMinVal = case config.pulsating of
      NoPulsating -> 1.0
      Pulsating r -> r.min
    pulsatingMaxVal = case config.pulsating of
      NoPulsating -> 1.0
      Pulsating r -> r.max
    pulseCenter = (pulsatingMinVal + pulsatingMaxVal) * 0.5
    pulseAmplitude = (pulsatingMaxVal - pulsatingMinVal) * 0.5
    pulseValue = case config.pulsating of
      NoPulsating -> 1.0
      Pulsating _ -> pulseCenter + pulseAmplitude * sin (time * config.speed * 3.0)
    
    baseIntensity1 = 0.45 + 0.15 * sin (time * config.speed * 1.5)
    baseIntensity2 = 0.3 + 0.2 * cos (time * config.speed * 1.1)
    intensity = max ((baseIntensity1 + baseIntensity2) * pulseValue) 0.55
  in
    { time: time
    , intensity: intensity
    , pulseValue: max pulseValue 0.9
    }

-- | WGSL Shader source (stored as data, not executed)
wgslShaderSource :: String
wgslShaderSource = """
  struct Uniforms {
    iTime: f32,
    _pad0: f32,
    iResolution: vec2<f32>,
    lightPos: vec2<f32>,
    lightDir: vec2<f32>,
    color: vec3<f32>, 
    speed: f32,
    lightSpread: f32,
    lightLength: f32,
    sourceWidth: f32,
    pulsating: f32,
    pulsatingMin: f32,
    pulsatingMax: f32,
    fadeDistance: f32,
    saturation: f32,
    noiseAmount: f32,
    distortion: f32,
    particlesEnabled: f32,
    particleAmount: f32,
    particleSizeMin: f32,
    particleSizeMax: f32,
    particleSpeed: f32,
    particleOpacity: f32,
    particleDrift: f32,
    _pad1: f32,
    _pad2: f32,
  };

  @group(0) @binding(0) var<uniform> uniforms: Uniforms;
  // ... rest of shader omitted for brevity, see source file
"""
