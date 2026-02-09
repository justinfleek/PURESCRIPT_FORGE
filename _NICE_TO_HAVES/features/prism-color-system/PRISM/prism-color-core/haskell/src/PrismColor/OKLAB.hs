{-# LANGUAGE StrictData #-}

-- |
-- Module      : PrismColor.OKLAB
-- Description : OKLAB/OKLCH perceptually uniform color space
-- 
-- OKLAB (Björn Ottosson, 2020) is a perceptually uniform color space
-- that improves on CIELAB. Key properties:
-- 
-- - Perceptual uniformity: equal steps in L, a, b appear equally different
-- - Hue linearity: blending colors preserves perceptual hue
-- - Lightness accuracy: L correlates with perceived brightness
-- 
-- OKLCH is the cylindrical form using Lightness, Chroma, Hue.
-- This is what we use for palette generation.

module PrismColor.OKLAB
  ( -- * XYZ ↔ OKLAB
    xyzToOklab
  , oklabToXYZ
  
    -- * OKLAB ↔ OKLCH
  , oklabToOklch
  , oklchToOklab
  
    -- * Full Conversion Chain
  , srgbToOklab
  , oklabToSrgb
  , srgbToOklch
  , oklchToSrgb
  
    -- * Utilities
  , oklchWithLightness
  , oklchWithChroma
  , oklchWithHue
  , oklchRotateHue
  ) where

import PrismColor.Types
import PrismColor.SRGB

-- | XYZ to OKLAB conversion
-- 
-- This uses an intermediate LMS cone response space:
-- XYZ → LMS → LMS' (cube root) → OKLAB
xyzToOklab :: XYZ -> OKLAB
xyzToOklab (XYZ x y z) =
  let -- XYZ to approximate cone response (LMS)
      l = 0.8189330101 * x + 0.3618667424 * y - 0.1288597137 * z
      m = 0.0329845436 * x + 0.9293118715 * y + 0.0361456387 * z
      s = 0.0482003018 * x + 0.2643662691 * y + 0.6338517070 * z
      
      -- Cube root (perceptual compression)
      l' = cbrt l
      m' = cbrt m
      s' = cbrt s
      
      -- LMS' to OKLAB
      okL = 0.2104542553 * l' + 0.7936177850 * m' - 0.0040720468 * s'
      okA = 1.9779984951 * l' - 2.4285922050 * m' + 0.4505937099 * s'
      okB = 0.0259040371 * l' + 0.7827717662 * m' - 0.8086757660 * s'
  in OKLAB
    { oklabL = clampUnit okL
    , oklabA = okA
    , oklabB = okB
    }
  where
    cbrt x = if x >= 0 then x ** (1/3) else -((-x) ** (1/3))

-- | OKLAB to XYZ conversion (inverse of xyzToOklab)
oklabToXYZ :: OKLAB -> XYZ
oklabToXYZ (OKLAB (UnitInterval okL) okA okB) =
  let -- OKLAB to LMS'
      l' = okL + 0.3963377774 * okA + 0.2158037573 * okB
      m' = okL - 0.1055613458 * okA - 0.0638541728 * okB
      s' = okL - 0.0894841775 * okA - 1.2914855480 * okB
      
      -- Cube (inverse of cube root)
      l = l' * l' * l'
      m = m' * m' * m'
      s = s' * s' * s'
      
      -- LMS to XYZ
      x =  1.2270138511 * l - 0.5577999807 * m + 0.2812561490 * s
      y = -0.0405801784 * l + 1.1122568696 * m - 0.0716766787 * s
      z = -0.0763812845 * l - 0.4214819784 * m + 1.5861632204 * s
  in XYZ
    { xyzX = max 0 x
    , xyzY = max 0 y
    , xyzZ = max 0 z
    }

-- | OKLAB to OKLCH (Cartesian to Cylindrical)
oklabToOklch :: OKLAB -> OKLCH
oklabToOklch (OKLAB l a b) =
  let chroma = sqrt (a * a + b * b)
      hueDeg = atan2 b a * (180 / pi)
  in OKLCH
    { oklchL = l
    , oklchC = max 0 chroma
    , oklchH = normalizeHue hueDeg
    }

-- | OKLCH to OKLAB (Cylindrical to Cartesian)
oklchToOklab :: OKLCH -> OKLAB
oklchToOklab (OKLCH l c (Hue h)) =
  let hRad = h * (pi / 180)
  in OKLAB
    { oklabL = l
    , oklabA = c * cos hRad
    , oklabB = c * sin hRad
    }

-- | sRGB to OKLAB (full chain)
srgbToOklab :: SRGB -> OKLAB
srgbToOklab = xyzToOklab . linearToXYZ . srgbToLinear

-- | OKLAB to sRGB (full chain)
oklabToSrgb :: OKLAB -> SRGB
oklabToSrgb = linearToSrgb . xyzToLinear . oklabToXYZ

-- | sRGB to OKLCH (full chain)
srgbToOklch :: SRGB -> OKLCH
srgbToOklch = oklabToOklch . srgbToOklab

-- | OKLCH to sRGB (full chain)
oklchToSrgb :: OKLCH -> SRGB
oklchToSrgb = oklabToSrgb . oklchToOklab

-- | Set lightness while preserving chroma and hue
oklchWithLightness :: Double -> OKLCH -> OKLCH
oklchWithLightness l' c = c { oklchL = clampUnit l' }

-- | Set chroma while preserving lightness and hue
oklchWithChroma :: Double -> OKLCH -> OKLCH
oklchWithChroma c' c = c { oklchC = max 0 c' }

-- | Set hue while preserving lightness and chroma
oklchWithHue :: Double -> OKLCH -> OKLCH
oklchWithHue h' c = c { oklchH = normalizeHue h' }

-- | Rotate hue by a given number of degrees
oklchRotateHue :: Double -> OKLCH -> OKLCH
oklchRotateHue delta c = c { oklchH = normalizeHue (unHue (oklchH c) + delta) }
