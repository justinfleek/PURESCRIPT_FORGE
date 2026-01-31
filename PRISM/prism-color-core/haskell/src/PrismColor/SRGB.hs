{-# LANGUAGE StrictData #-}

-- |
-- Module      : PrismColor.SRGB
-- Description : sRGB color space conversions
-- 
-- Implements the sRGB transfer function (gamma correction) and
-- conversion to/from CIE XYZ color space.
-- 
-- The sRGB standard uses:
-- - D65 white point
-- - Rec. 709 primaries
-- - Piecewise transfer function (gamma ≈ 2.4)

module PrismColor.SRGB
  ( -- * sRGB Transfer Function
    srgbToLinear
  , linearToSrgb
  , srgbToLinearComponent
  , linearToSrgbComponent
  
    -- * XYZ Conversion
  , linearToXYZ
  , xyzToLinear
  
    -- * Relative Luminance (WCAG)
  , relativeLuminance
  
    -- * Hex Conversion
  , srgbToHex
  , hexToSrgb
  ) where

import PrismColor.Types
import Data.Char (intToDigit)
import Text.Read (readMaybe)
import Numeric (readHex)

-- | sRGB to Linear RGB component conversion (gamma expansion)
-- 
-- Uses the official sRGB transfer function:
-- - Linear region: V / 12.92 for V ≤ 0.04045
-- - Gamma region: ((V + 0.055) / 1.055)^2.4 for V > 0.04045
srgbToLinearComponent :: UnitInterval -> UnitInterval
srgbToLinearComponent (UnitInterval v)
  | v <= 0.04045 = clampUnit (v / 12.92)
  | otherwise    = clampUnit (((v + 0.055) / 1.055) ** 2.4)

-- | Linear to sRGB component conversion (gamma compression)
-- 
-- Inverse of srgbToLinearComponent:
-- - Linear region: 12.92 * V for V ≤ 0.0031308
-- - Gamma region: 1.055 * V^(1/2.4) - 0.055 for V > 0.0031308
linearToSrgbComponent :: UnitInterval -> UnitInterval
linearToSrgbComponent (UnitInterval v)
  | v <= 0.0031308 = clampUnit (12.92 * v)
  | otherwise      = clampUnit (1.055 * (v ** (1/2.4)) - 0.055)

-- | Convert sRGB to Linear RGB
srgbToLinear :: SRGB -> LinearRGB
srgbToLinear (SRGB r g b) = LinearRGB
  { linR = srgbToLinearComponent r
  , linG = srgbToLinearComponent g
  , linB = srgbToLinearComponent b
  }

-- | Convert Linear RGB to sRGB
linearToSrgb :: LinearRGB -> SRGB
linearToSrgb (LinearRGB r g b) = SRGB
  { srgbR = linearToSrgbComponent r
  , srgbG = linearToSrgbComponent g
  , srgbB = linearToSrgbComponent b
  }

-- | Linear RGB to CIE XYZ (D65 white point, sRGB primaries)
-- 
-- Matrix from IEC 61966-2-1:1999:
-- ┌     ┐   ┌                                    ┐ ┌   ┐
-- │ X   │   │ 0.4124564  0.3575761  0.1804375   │ │ R │
-- │ Y   │ = │ 0.2126729  0.7151522  0.0721750   │ │ G │
-- │ Z   │   │ 0.0193339  0.1191920  0.9503041   │ │ B │
-- └     ┘   └                                    ┘ └   ┘
linearToXYZ :: LinearRGB -> XYZ
linearToXYZ (LinearRGB (UnitInterval r) (UnitInterval g) (UnitInterval b)) = XYZ
  { xyzX = 0.4124564 * r + 0.3575761 * g + 0.1804375 * b
  , xyzY = 0.2126729 * r + 0.7151522 * g + 0.0721750 * b
  , xyzZ = 0.0193339 * r + 0.1191920 * g + 0.9503041 * b
  }

-- | CIE XYZ to Linear RGB (inverse of above)
-- 
-- ┌     ┐   ┌                                      ┐ ┌   ┐
-- │ R   │   │  3.2404542  -1.5371385  -0.4985314  │ │ X │
-- │ G   │ = │ -0.9692660   1.8760108   0.0415560  │ │ Y │
-- │ B   │   │  0.0556434  -0.2040259   1.0572252  │ │ Z │
-- └     ┘   └                                      ┘ └   ┘
-- 
-- Note: Result is clamped to [0,1] for out-of-gamut colors
xyzToLinear :: XYZ -> LinearRGB
xyzToLinear (XYZ x y z) = LinearRGB
  { linR = clampUnit ( 3.2404542 * x - 1.5371385 * y - 0.4985314 * z)
  , linG = clampUnit (-0.9692660 * x + 1.8760108 * y + 0.0415560 * z)
  , linB = clampUnit ( 0.0556434 * x - 0.2040259 * y + 1.0572252 * z)
  }

-- | Relative luminance from sRGB (WCAG 2.1 definition)
-- 
-- L = 0.2126 * R + 0.7152 * G + 0.0722 * B
-- 
-- where R, G, B are linear RGB values.
-- 
-- This is identical to the Y component of XYZ.
relativeLuminance :: SRGB -> Double
relativeLuminance color =
  let LinearRGB (UnitInterval r) (UnitInterval g) (UnitInterval b) = srgbToLinear color
  in 0.2126 * r + 0.7152 * g + 0.0722 * b

-- | Convert sRGB to hex string (e.g., "#ff5733")
srgbToHex :: SRGB -> String
srgbToHex (SRGB (UnitInterval r) (UnitInterval g) (UnitInterval b)) =
  '#' : toHex (round (r * 255)) ++ toHex (round (g * 255)) ++ toHex (round (b * 255))
  where
    toHex :: Int -> String
    toHex n = [intToDigit (n `div` 16), intToDigit (n `mod` 16)]

-- | Parse hex string to sRGB (e.g., "#ff5733" or "ff5733")
hexToSrgb :: String -> Maybe SRGB
hexToSrgb s = do
  let hex = dropWhile (== '#') s
  guard (length hex == 6)
  [(r, _)] <- pure $ readHex (take 2 hex)
  [(g, _)] <- pure $ readHex (take 2 (drop 2 hex))
  [(b, _)] <- pure $ readHex (drop 4 hex)
  pure $ SRGB
    { srgbR = clampUnit (fromIntegral (r :: Int) / 255)
    , srgbG = clampUnit (fromIntegral (g :: Int) / 255)
    , srgbB = clampUnit (fromIntegral (b :: Int) / 255)
    }
  where
    guard True = Just ()
    guard False = Nothing
