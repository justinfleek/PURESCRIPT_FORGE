{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StrictData #-}

-- |
-- Module      : PrismColor.Types
-- Description : Core color types with smart constructors
-- 
-- All color values use smart constructors to ensure bounds are respected.
-- This mirrors the Lean4 formalization where UnitInterval requires proofs.

module PrismColor.Types
  ( -- * Bounded Types
    UnitInterval
  , mkUnitInterval
  , clampUnit
  , unUnit
  , Hue
  , mkHue
  , normalizeHue
  , unHue
  
    -- * Color Spaces
  , SRGB(..)
  , LinearRGB(..)
  , XYZ(..)
  , OKLAB(..)
  , OKLCH(..)
  
    -- * Configuration
  , MonitorType(..)
  , ThemeMode(..)
  , BlackBalance
  , mkBlackBalance
  , defaultBlackBalance
  , unBlackBalance
  , ThemeConfig(..)
  
    -- * Palette
  , Base16Colors(..)
  , ThemeVariant(..)
  ) where

import Data.Aeson (FromJSON, ToJSON)
import GHC.Generics (Generic)

-- | Value bounded in [0, 1]
newtype UnitInterval = UnitInterval { unUnit :: Double }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (FromJSON, ToJSON)

-- | Smart constructor that validates bounds
mkUnitInterval :: Double -> Maybe UnitInterval
mkUnitInterval x
  | x >= 0 && x <= 1 = Just (UnitInterval x)
  | otherwise = Nothing

-- | Clamp to [0, 1]
clampUnit :: Double -> UnitInterval
clampUnit x = UnitInterval (max 0 (min 1 x))

-- | Hue angle in degrees [0, 360)
newtype Hue = Hue { unHue :: Double }
  deriving stock (Eq, Show, Generic)
  deriving newtype (FromJSON, ToJSON)

-- | Smart constructor that validates bounds
mkHue :: Double -> Maybe Hue
mkHue x
  | x >= 0 && x < 360 = Just (Hue x)
  | otherwise = Nothing

-- | Normalize any angle to [0, 360)
normalizeHue :: Double -> Hue
normalizeHue x = Hue (x - 360 * fromIntegral (floor (x / 360) :: Int))

-- | sRGB color space (gamma-corrected device color)
data SRGB = SRGB
  { srgbR :: !UnitInterval
  , srgbG :: !UnitInterval
  , srgbB :: !UnitInterval
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | Linear RGB (physical light intensity, no gamma)
data LinearRGB = LinearRGB
  { linR :: !UnitInterval
  , linG :: !UnitInterval
  , linB :: !UnitInterval
  }
  deriving stock (Eq, Show, Generic)

-- | CIE XYZ color space with D65 white point
data XYZ = XYZ
  { xyzX :: !Double
  , xyzY :: !Double  -- Y is luminance
  , xyzZ :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | OKLAB perceptually uniform color space
data OKLAB = OKLAB
  { oklabL :: !UnitInterval  -- Lightness [0, 1]
  , oklabA :: !Double        -- Green-Red axis (typically [-0.4, 0.4])
  , oklabB :: !Double        -- Blue-Yellow axis
  }
  deriving stock (Eq, Show, Generic)

-- | OKLCH cylindrical form of OKLAB
data OKLCH = OKLCH
  { oklchL :: !UnitInterval  -- Lightness [0, 1]
  , oklchC :: !Double        -- Chroma (≥ 0, typically [0, 0.4])
  , oklchH :: !Hue           -- Hue angle [0, 360)
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | Monitor type affects optimal black balance
data MonitorType
  = OLED  -- ^ Optimal black balance ~11%
  | LCD   -- ^ Optimal black balance ~16%
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | Theme mode
data ThemeMode
  = Dark
  | Light
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | Black balance as a bounded percentage [0, 0.20]
newtype BlackBalance = BlackBalance { unBlackBalance :: Double }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (FromJSON, ToJSON)

-- | Smart constructor that validates bounds
mkBlackBalance :: Double -> Maybe BlackBalance
mkBlackBalance x
  | x >= 0 && x <= 0.20 = Just (BlackBalance x)
  | otherwise = Nothing

-- | Default black balance for monitor type
defaultBlackBalance :: MonitorType -> BlackBalance
defaultBlackBalance OLED = BlackBalance 0.11
defaultBlackBalance LCD  = BlackBalance 0.16

-- | Theme configuration
data ThemeConfig = ThemeConfig
  { configBaseHue        :: !Hue
  , configBaseSaturation :: !UnitInterval
  , configHeroHue        :: !Hue
  , configHeroSaturation :: !UnitInterval
  , configMonitorType    :: !MonitorType
  , configBlackBalance   :: !BlackBalance
  , configMode           :: !ThemeMode
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | Base16 color palette
data Base16Colors = Base16Colors
  { base00 :: !String  -- Background
  , base01 :: !String  -- Lighter background
  , base02 :: !String  -- Selection
  , base03 :: !String  -- Comments
  , base04 :: !String  -- Dark foreground
  , base05 :: !String  -- Default foreground
  , base06 :: !String  -- Light foreground
  , base07 :: !String  -- Brightest
  , base08 :: !String  -- Error/Red
  , base09 :: !String  -- Warning/Orange
  , base0A :: !String  -- Hero accent
  , base0B :: !String  -- Success/Green
  , base0C :: !String  -- Info/Cyan
  , base0D :: !String  -- Link/Blue
  , base0E :: !String  -- Special/Purple
  , base0F :: !String  -- Deprecated
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | Generated theme variant
data ThemeVariant = ThemeVariant
  { variantName               :: !String
  , variantBackgroundLightness :: !Double
  , variantColors             :: !Base16Colors
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)
