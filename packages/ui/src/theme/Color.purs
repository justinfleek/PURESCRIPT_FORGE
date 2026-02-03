-- | Color Utilities - PRISM Color Space Conversions
-- |
-- | Complete color conversion chain based on PRISM color science:
-- |   sRGB <-> Linear RGB <-> XYZ (D65) <-> OKLAB <-> OKLCH
-- |
-- | Each conversion is mathematically bijective (proven in Lean4).
-- | OKLCH is the target space for perceptually uniform palette generation.
-- |
-- | Reference: src/prism-lean/PrismColor/Conversions.lean
-- | Reference: src/prism-hs/src/PrismColor/OKLAB.hs
module Forge.UI.Theme.Color
  ( -- * Hex Conversions
    hexToRgb
  , rgbToHex
  , hexToSrgb
  , srgbToHex
  
    -- * sRGB <-> Linear RGB (Gamma)
  , srgbToLinear
  , linearToSrgb
  , srgbToLinearComponent
  , linearToSrgbComponent
  
    -- * Linear RGB <-> XYZ
  , linearToXYZ
  , xyzToLinear
  
    -- * XYZ <-> OKLAB
  , xyzToOklab
  , oklabToXYZ
  
    -- * OKLAB <-> OKLCH
  , oklabToOklch
  , oklchToOklab
  
    -- * Full Chain Conversions
  , srgbToOklch
  , oklchToSrgb
  , hexToOklch
  , oklchToHex
  
    -- * Relative Luminance (WCAG)
  , relativeLuminance
  , relativeLuminanceHex
  
    -- * OKLCH Utilities
  , oklchWithLightness
  , oklchWithChroma
  , oklchWithHue
  , oklchRotateHue
  
    -- * Legacy Compatibility
  , generateScale
  , generateNeutralScale
  , generateAlphaScale
  , mixColors
  , lighten
  , darken
  , withAlpha
  , RGB
  ) where

import Prelude

import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.String.CodeUnits as CU
import Forge.UI.Theme.Types (HexColor, LinearRGB, OKLAB, OKLCH, RGB, SRGB, UnitInterval, XYZ, Hue, clampUnit, mkOKLCH, normalizeHue, unHue, unUnit)
import Math (atan2, cos, floor, max, min, pi, pow, sin, sqrt)

-------------------------------------------------------------------------------
-- HEX CONVERSIONS
-------------------------------------------------------------------------------

-- | Convert hex color to RGB (0-1 range, unbounded)
hexToRgb :: HexColor -> RGB
hexToRgb hex =
  let
    h = String.drop 1 hex  -- Remove #
    full = if String.length h == 3
           then expandShortHex h
           else h
    rHex = String.take 2 full
    gHex = String.take 2 (String.drop 2 full)
    bHex = String.take 2 (String.drop 4 full)
    r = fromMaybe 0 (Int.fromStringAs Int.hexadecimal rHex)
    g = fromMaybe 0 (Int.fromStringAs Int.hexadecimal gHex)
    b = fromMaybe 0 (Int.fromStringAs Int.hexadecimal bHex)
  in
    { r: Int.toNumber r / 255.0
    , g: Int.toNumber g / 255.0
    , b: Int.toNumber b / 255.0
    }
  where
    expandShortHex :: String -> String
    expandShortHex s = 
      let chars = CU.toCharArray s
      in case chars of
        [c1, c2, c3] -> 
          CU.fromCharArray [c1, c1, c2, c2, c3, c3]
        _ -> s

-- | Convert hex to bounded SRGB
hexToSrgb :: HexColor -> SRGB
hexToSrgb hex =
  let { r, g, b } = hexToRgb hex
  in { r: clampUnit r, g: clampUnit g, b: clampUnit b }

-- | Convert RGB (0-1 range) to hex color
rgbToHex :: Number -> Number -> Number -> HexColor
rgbToHex r g b =
  let
    toHex v = 
      let 
        clamped = max 0.0 (min 1.0 v)
        int = Int.round (clamped * 255.0)
        hex = Int.toStringAs Int.hexadecimal int
      in if String.length hex == 1 then "0" <> hex else hex
  in "#" <> toHex r <> toHex g <> toHex b

-- | Convert bounded SRGB to hex
srgbToHex :: SRGB -> HexColor
srgbToHex { r, g, b } = rgbToHex (unUnit r) (unUnit g) (unUnit b)

-------------------------------------------------------------------------------
-- sRGB <-> LINEAR RGB (GAMMA TRANSFER FUNCTION)
-- Proven bijective in Lean4: srgb_linear_roundtrip theorem
-------------------------------------------------------------------------------

-- | sRGB gamma expansion for single component (sRGB -> Linear)
-- | Threshold: 0.04045 (sRGB standard)
-- | Mirrors Lean4 srgbToLinearComponent
srgbToLinearComponent :: UnitInterval -> UnitInterval
srgbToLinearComponent ui =
  let x = unUnit ui
  in if x <= 0.04045
     then clampUnit (x / 12.92)
     else clampUnit (pow ((x + 0.055) / 1.055) 2.4)

-- | sRGB gamma compression for single component (Linear -> sRGB)
-- | Threshold: 0.0031308 (corresponding linear value)
-- | Mirrors Lean4 linearToSrgbComponent
linearToSrgbComponent :: UnitInterval -> UnitInterval
linearToSrgbComponent ui =
  let x = unUnit ui
  in if x <= 0.0031308
     then clampUnit (12.92 * x)
     else clampUnit (1.055 * pow x (1.0 / 2.4) - 0.055)

-- | Convert sRGB to Linear RGB
srgbToLinear :: SRGB -> LinearRGB
srgbToLinear { r, g, b } =
  { r: srgbToLinearComponent r
  , g: srgbToLinearComponent g
  , b: srgbToLinearComponent b
  }

-- | Convert Linear RGB to sRGB
linearToSrgb :: LinearRGB -> SRGB
linearToSrgb { r, g, b } =
  { r: linearToSrgbComponent r
  , g: linearToSrgbComponent g
  , b: linearToSrgbComponent b
  }

-------------------------------------------------------------------------------
-- LINEAR RGB <-> XYZ (D65 WHITE POINT)
-- Standard sRGB to XYZ matrix transformation
-------------------------------------------------------------------------------

-- | Convert Linear RGB to XYZ (D65 white point)
-- | The Y component is luminance (used for WCAG contrast)
linearToXYZ :: LinearRGB -> XYZ
linearToXYZ { r, g, b } =
  let
    rv = unUnit r
    gv = unUnit g
    bv = unUnit b
  in
    { x: 0.4124564 * rv + 0.3575761 * gv + 0.1804375 * bv
    , y: 0.2126729 * rv + 0.7151522 * gv + 0.0721750 * bv  -- Luminance
    , z: 0.0193339 * rv + 0.1191920 * gv + 0.9503041 * bv
    }

-- | Convert XYZ to Linear RGB (inverse matrix)
xyzToLinear :: XYZ -> LinearRGB
xyzToLinear { x, y, z } =
  { r: clampUnit ( 3.2404542 * x - 1.5371385 * y - 0.4985314 * z)
  , g: clampUnit (-0.9692660 * x + 1.8760108 * y + 0.0415560 * z)
  , b: clampUnit ( 0.0556434 * x - 0.2040259 * y + 1.0572252 * z)
  }

-------------------------------------------------------------------------------
-- XYZ <-> OKLAB
-- OKLAB (Bjorn Ottosson, 2020) is perceptually uniform
-------------------------------------------------------------------------------

-- | Cube root function (handles negative values)
cbrt :: Number -> Number
cbrt x = if x >= 0.0 then pow x (1.0/3.0) else negate (pow (negate x) (1.0/3.0))

-- | Convert XYZ to OKLAB via LMS intermediate
-- | Mirrors Haskell xyzToOklab in src/prism-hs/src/PrismColor/OKLAB.hs
xyzToOklab :: XYZ -> OKLAB
xyzToOklab { x, y, z } =
  let
    -- XYZ to approximate cone response (LMS)
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
  in
    { l: clampUnit okL
    , a: okA
    , b: okB
    }

-- | Convert OKLAB to XYZ (inverse transformation)
oklabToXYZ :: OKLAB -> XYZ
oklabToXYZ { l, a, b } =
  let
    okL = unUnit l
    
    -- OKLAB to LMS'
    l' = okL + 0.3963377774 * a + 0.2158037573 * b
    m' = okL - 0.1055613458 * a - 0.0638541728 * b
    s' = okL - 0.0894841775 * a - 1.2914855480 * b
    
    -- Cube (inverse of cube root)
    lms_l = l' * l' * l'
    lms_m = m' * m' * m'
    lms_s = s' * s' * s'
    
    -- LMS to XYZ
    xv =  1.2270138511 * lms_l - 0.5577999807 * lms_m + 0.2812561490 * lms_s
    yv = -0.0405801784 * lms_l + 1.1122568696 * lms_m - 0.0716766787 * lms_s
    zv = -0.0763812845 * lms_l - 0.4214819784 * lms_m + 1.5861632204 * lms_s
  in
    { x: max 0.0 xv
    , y: max 0.0 yv
    , z: max 0.0 zv
    }

-------------------------------------------------------------------------------
-- OKLAB <-> OKLCH (CARTESIAN <-> CYLINDRICAL)
-- Proven bijective in Lean4: oklab_oklch_roundtrip theorem
-------------------------------------------------------------------------------

-- | Convert OKLAB (Cartesian) to OKLCH (Cylindrical)
-- | Chroma = sqrt(a^2 + b^2), Hue = atan2(b, a)
oklabToOklch :: OKLAB -> OKLCH
oklabToOklch { l, a, b } =
  let
    chroma = sqrt (a * a + b * b)
    hueDeg = atan2 b a * (180.0 / pi)
  in
    { l: l
    , c: max 0.0 chroma
    , h: normalizeHue hueDeg
    }

-- | Convert OKLCH (Cylindrical) to OKLAB (Cartesian)
-- | a = c * cos(h), b = c * sin(h)
oklchToOklab :: OKLCH -> OKLAB
oklchToOklab { l, c, h } =
  let
    hRad = unHue h * (pi / 180.0)
  in
    { l: l
    , a: c * cos hRad
    , b: c * sin hRad
    }

-------------------------------------------------------------------------------
-- FULL CHAIN CONVERSIONS
-------------------------------------------------------------------------------

-- | sRGB to OKLCH (full chain)
srgbToOklch :: SRGB -> OKLCH
srgbToOklch = oklabToOklch <<< xyzToOklab <<< linearToXYZ <<< srgbToLinear

-- | OKLCH to sRGB (full chain)
oklchToSrgb :: OKLCH -> SRGB
oklchToSrgb = linearToSrgb <<< xyzToLinear <<< oklabToXYZ <<< oklchToOklab

-- | Hex to OKLCH
hexToOklch :: HexColor -> OKLCH
hexToOklch = srgbToOklch <<< hexToSrgb

-- | OKLCH to Hex
oklchToHex :: OKLCH -> HexColor
oklchToHex = srgbToHex <<< oklchToSrgb

-------------------------------------------------------------------------------
-- RELATIVE LUMINANCE (WCAG)
-------------------------------------------------------------------------------

-- | Calculate relative luminance from sRGB (WCAG 2.1 definition)
-- | L = 0.2126 * R + 0.7152 * G + 0.0722 * B (in linear space)
-- | Used for contrast ratio calculations
relativeLuminance :: SRGB -> Number
relativeLuminance srgb =
  let lin = srgbToLinear srgb
  in 0.2126 * unUnit lin.r + 0.7152 * unUnit lin.g + 0.0722 * unUnit lin.b

-- | Calculate relative luminance from hex color
relativeLuminanceHex :: HexColor -> Number
relativeLuminanceHex = relativeLuminance <<< hexToSrgb

-------------------------------------------------------------------------------
-- OKLCH UTILITIES
-------------------------------------------------------------------------------

-- | Set lightness while preserving chroma and hue
oklchWithLightness :: Number -> OKLCH -> OKLCH
oklchWithLightness l' c = c { l = clampUnit l' }

-- | Set chroma while preserving lightness and hue
oklchWithChroma :: Number -> OKLCH -> OKLCH
oklchWithChroma c' oklch = oklch { c = max 0.0 c' }

-- | Set hue while preserving lightness and chroma
oklchWithHue :: Number -> OKLCH -> OKLCH
oklchWithHue h' oklch = oklch { h = normalizeHue h' }

-- | Rotate hue by a given number of degrees
oklchRotateHue :: Number -> OKLCH -> OKLCH
oklchRotateHue delta oklch = oklch { h = normalizeHue (unHue oklch.h + delta) }

-------------------------------------------------------------------------------
-- LEGACY COMPATIBILITY (for existing Resolve.purs)
-------------------------------------------------------------------------------

-- | Generate a 12-step color scale from a seed color
generateScale :: HexColor -> Boolean -> Array HexColor
generateScale seed isDark =
  let
    base = hexToOklch seed
    lightSteps = if isDark
      then [0.15, 0.18, 0.22, 0.26, 0.32, 0.38, 0.46, 0.56, unUnit base.l, unUnit base.l - 0.05, 0.75, 0.93]
      else [0.99, 0.97, 0.94, 0.9, 0.85, 0.79, 0.72, 0.64, unUnit base.l, unUnit base.l + 0.05, 0.45, 0.25]
    chromaMultipliers = if isDark
      then [0.15, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.85, 1.0, 1.0, 0.9, 0.6]
      else [0.1, 0.15, 0.25, 0.35, 0.45, 0.55, 0.7, 0.85, 1.0, 1.0, 0.95, 0.85]
  in
    Array.zipWith (\lStep cMult -> 
      oklchToHex (mkOKLCH lStep (base.c * cMult) (unHue base.h))
    ) lightSteps chromaMultipliers

-- | Generate a neutral (low chroma) scale
generateNeutralScale :: HexColor -> Boolean -> Array HexColor
generateNeutralScale seed isDark =
  let
    base = hexToOklch seed
    neutralChroma = min base.c 0.02
    lightSteps = if isDark
      then [0.13, 0.16, 0.2, 0.24, 0.28, 0.33, 0.4, 0.52, 0.58, 0.66, 0.82, 0.96]
      else [0.995, 0.98, 0.96, 0.94, 0.91, 0.88, 0.84, 0.78, 0.62, 0.56, 0.46, 0.2]
  in
    map (\lStep -> oklchToHex (mkOKLCH lStep neutralChroma (unHue base.h))) lightSteps

-- | Generate an alpha-blended scale
generateAlphaScale :: Array HexColor -> Boolean -> Array HexColor
generateAlphaScale scale isDark =
  let
    alphas = if isDark
      then [0.02, 0.04, 0.08, 0.12, 0.16, 0.2, 0.26, 0.36, 0.44, 0.52, 0.76, 0.96]
      else [0.01, 0.03, 0.06, 0.09, 0.12, 0.15, 0.2, 0.28, 0.48, 0.56, 0.64, 0.88]
    bg = if isDark then 0.0 else 1.0
  in
    Array.zipWith (\hex alpha ->
      let { r, g, b } = hexToRgb hex
          blendedR = r * alpha + bg * (1.0 - alpha)
          blendedG = g * alpha + bg * (1.0 - alpha)
          blendedB = b * alpha + bg * (1.0 - alpha)
      in rgbToHex blendedR blendedG blendedB
    ) scale alphas

-- | Mix two colors by an amount (0-1)
mixColors :: HexColor -> HexColor -> Number -> HexColor
mixColors color1 color2 amount =
  let
    c1 = hexToOklch color1
    c2 = hexToOklch color2
  in oklchToHex $ mkOKLCH
    (unUnit c1.l + (unUnit c2.l - unUnit c1.l) * amount)
    (c1.c + (c2.c - c1.c) * amount)
    (unHue c1.h + (unHue c2.h - unHue c1.h) * amount)

-- | Lighten a color by an amount
lighten :: HexColor -> Number -> HexColor
lighten color amount =
  let oklch = hexToOklch color
  in oklchToHex $ mkOKLCH (min 1.0 (unUnit oklch.l + amount)) oklch.c (unHue oklch.h)

-- | Darken a color by an amount
darken :: HexColor -> Number -> HexColor
darken color amount =
  let oklch = hexToOklch color
  in oklchToHex $ mkOKLCH (max 0.0 (unUnit oklch.l - amount)) oklch.c (unHue oklch.h)

-- | Create an RGBA string from a hex color and alpha
withAlpha :: HexColor -> Number -> String
withAlpha color alpha =
  let { r, g, b } = hexToRgb color
  in "rgba(" <> show (Int.round (r * 255.0)) <> ", " 
             <> show (Int.round (g * 255.0)) <> ", " 
             <> show (Int.round (b * 255.0)) <> ", " 
             <> show alpha <> ")"
