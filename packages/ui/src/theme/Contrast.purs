-- | Contrast - WCAG 2.1 Contrast Ratio Calculations
-- |
-- | Implements WCAG 2.1 contrast ratio formula:
-- |   CR = (L1 + 0.05) / (L2 + 0.05)
-- |
-- | Where L1 is the lighter luminance and L2 is the darker.
-- |
-- | WCAG Requirements:
-- | - AA Normal text: CR >= 4.5:1
-- | - AA Large text:  CR >= 3:1
-- | - AAA Normal:     CR >= 7:1
-- | - AAA Large:      CR >= 4.5:1
-- |
-- | Reference: src/prism-lean/PrismColor/Contrast.lean
-- | Reference: src/prism-hs/src/PrismColor/Contrast.hs
module Forge.UI.Theme.Contrast
  ( -- * Contrast Ratio
    contrastRatio
  , contrastRatioHex
  , contrastRatioSrgb
  
    -- * WCAG Compliance
  , WCAGLevel(..)
  , TextSize(..)
  , wcagCompliance
  , meetsWCAG
  , meetsWCAGHex
  , minContrastFor
  
    -- * Finding Compliant Colors
  , adjustLightnessForContrast
  , findAccessibleLightness
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Forge.UI.Theme.Color (hexToOklch, hexToSrgb, oklchToHex, oklchToSrgb, oklchWithLightness, relativeLuminance)
import Forge.UI.Theme.Types (HexColor, OKLCH, SRGB, clampUnit, unUnit)
import Math (abs, max, min)

-------------------------------------------------------------------------------
-- WCAG LEVELS AND TEXT SIZES
-------------------------------------------------------------------------------

-- | WCAG compliance level
data WCAGLevel = AA | AAA

derive instance eqWCAGLevel :: Eq WCAGLevel
derive instance ordWCAGLevel :: Ord WCAGLevel

instance showWCAGLevel :: Show WCAGLevel where
  show AA = "AA"
  show AAA = "AAA"

-- | Text size category (affects required contrast)
data TextSize = NormalText | LargeText

derive instance eqTextSize :: Eq TextSize

instance showTextSize :: Show TextSize where
  show NormalText = "NormalText"
  show LargeText = "LargeText"

-------------------------------------------------------------------------------
-- CONTRAST RATIO CALCULATIONS
-------------------------------------------------------------------------------

-- | Calculate contrast ratio between two relative luminance values
-- |
-- | Formula: CR = (max(L1, L2) + 0.05) / (min(L1, L2) + 0.05)
-- |
-- | Properties (proven in Lean4 Contrast.lean):
-- | - CR >= 1 for all valid inputs
-- | - CR is symmetric: contrastRatio a b = contrastRatio b a
-- | - Maximum CR is 21:1 (white vs black)
contrastRatio :: Number -> Number -> Number
contrastRatio l1 l2 =
  let
    lighter = max l1 l2
    darker = min l1 l2
  in
    (lighter + 0.05) / (darker + 0.05)

-- | Contrast ratio between two sRGB colors
contrastRatioSrgb :: SRGB -> SRGB -> Number
contrastRatioSrgb c1 c2 =
  contrastRatio (relativeLuminance c1) (relativeLuminance c2)

-- | Contrast ratio between two hex colors
contrastRatioHex :: HexColor -> HexColor -> Number
contrastRatioHex hex1 hex2 =
  contrastRatioSrgb (hexToSrgb hex1) (hexToSrgb hex2)

-------------------------------------------------------------------------------
-- WCAG COMPLIANCE
-------------------------------------------------------------------------------

-- | Minimum contrast ratio required for WCAG compliance
minContrastFor :: WCAGLevel -> TextSize -> Number
minContrastFor AA NormalText = 4.5
minContrastFor AA LargeText = 3.0
minContrastFor AAA NormalText = 7.0
minContrastFor AAA LargeText = 4.5

-- | Check if a contrast ratio meets WCAG requirements
wcagCompliance :: Number -> WCAGLevel -> TextSize -> Boolean
wcagCompliance cr level size = cr >= minContrastFor level size

-- | Check if two sRGB colors meet WCAG requirements
meetsWCAG :: SRGB -> SRGB -> WCAGLevel -> TextSize -> Boolean
meetsWCAG c1 c2 level size =
  wcagCompliance (contrastRatioSrgb c1 c2) level size

-- | Check if two hex colors meet WCAG requirements
meetsWCAGHex :: HexColor -> HexColor -> WCAGLevel -> TextSize -> Boolean
meetsWCAGHex hex1 hex2 level size =
  wcagCompliance (contrastRatioHex hex1 hex2) level size

-------------------------------------------------------------------------------
-- FINDING COMPLIANT COLORS
-------------------------------------------------------------------------------

-- | Adjust lightness of an OKLCH color to achieve target contrast with background
-- |
-- | Uses binary search to find the minimal lightness adjustment
-- | that achieves the target contrast ratio.
-- |
-- | Returns Nothing if the target contrast is impossible to achieve.
-- |
-- | Parameters:
-- | - color: The OKLCH color to adjust
-- | - bgHex: Background color (as hex)
-- | - targetCR: Target contrast ratio (e.g., 4.5 for WCAG AA)
-- | - makeLighter: True to search toward white, False toward black
adjustLightnessForContrast 
  :: OKLCH 
  -> HexColor 
  -> Number 
  -> Boolean 
  -> Maybe OKLCH
adjustLightnessForContrast color bgHex targetCR makeLighter =
  let
    bgLum = relativeLuminance (hexToSrgb bgHex)
    
    -- Binary search for the right lightness
    search :: Int -> Number -> Number -> Maybe OKLCH
    search iterations lo hi
      | iterations > 50 = Nothing  -- Give up after 50 iterations
      | otherwise =
          let
            mid = (lo + hi) / 2.0
            candidate = oklchWithLightness mid color
            candidateSrgb = oklchToSrgb candidate
            candidateLum = relativeLuminance candidateSrgb
            cr = contrastRatio candidateLum bgLum
          in
            if abs (cr - targetCR) < 0.01
              then Just candidate
              else if cr < targetCR
                then if makeLighter
                     then search (iterations + 1) mid hi
                     else search (iterations + 1) lo mid
                else if makeLighter
                     then search (iterations + 1) lo mid
                     else search (iterations + 1) mid hi
    
    startL = unUnit color.l
  in
    if makeLighter
      then search 0 startL 1.0
      else search 0 0.0 startL

-- | Find an accessible lightness for a color against a background
-- |
-- | This is a convenience wrapper that returns a hex color.
-- | Tries lighter first (for dark backgrounds), darker first (for light backgrounds).
findAccessibleLightness 
  :: HexColor 
  -> HexColor 
  -> WCAGLevel 
  -> TextSize 
  -> Maybe HexColor
findAccessibleLightness fgHex bgHex level size =
  let
    targetCR = minContrastFor level size
    fg = hexToOklch fgHex
    bgLum = relativeLuminance (hexToSrgb bgHex)
    
    -- If background is dark, try making foreground lighter first
    tryLighter = bgLum < 0.5
  in
    case adjustLightnessForContrast fg bgHex targetCR tryLighter of
      Just result -> Just (oklchToHex result)
      Nothing -> 
        -- Try the opposite direction
        case adjustLightnessForContrast fg bgHex targetCR (not tryLighter) of
          Just result -> Just (oklchToHex result)
          Nothing -> Nothing


