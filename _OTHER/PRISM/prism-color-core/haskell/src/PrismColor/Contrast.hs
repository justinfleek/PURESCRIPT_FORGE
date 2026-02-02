{-# LANGUAGE StrictData #-}

-- |
-- Module      : PrismColor.Contrast
-- Description : WCAG 2.1 contrast ratio calculations
-- 
-- Implements WCAG 2.1 contrast ratio formula:
-- 
--   CR = (L1 + 0.05) / (L2 + 0.05)
-- 
-- where L1 is the lighter luminance and L2 is the darker.
-- 
-- WCAG requirements:
-- - AA Normal text: CR ≥ 4.5:1
-- - AA Large text:  CR ≥ 3:1
-- - AAA Normal:     CR ≥ 7:1
-- - AAA Large:      CR ≥ 4.5:1

module PrismColor.Contrast
  ( -- * Contrast Ratio
    contrastRatio
  , contrastRatioSRGB
  
    -- * WCAG Compliance
  , WCAGLevel(..)
  , TextSize(..)
  , wcagCompliance
  , meetsWCAG
  , minContrastFor
  
    -- * Finding Compliant Colors
  , adjustLightnessForContrast
  ) where

import PrismColor.Types
import PrismColor.SRGB
import PrismColor.OKLAB

-- | WCAG compliance level
data WCAGLevel = AA | AAA
  deriving (Eq, Ord, Show)

-- | Text size category
data TextSize = NormalText | LargeText
  deriving (Eq, Show)

-- | Calculate contrast ratio between two relative luminance values
-- 
-- The formula ensures the lighter color is always in the numerator:
--   CR = (max(L1, L2) + 0.05) / (min(L1, L2) + 0.05)
-- 
-- Properties (proven in Lean4):
-- - CR ≥ 1 for all valid inputs
-- - CR is symmetric: contrastRatio a b = contrastRatio b a
-- - Maximum CR is 21:1 (white vs black)
contrastRatio :: Double -> Double -> Double
contrastRatio l1 l2 =
  let lighter = max l1 l2
      darker = min l1 l2
  in (lighter + 0.05) / (darker + 0.05)

-- | Contrast ratio between two sRGB colors
contrastRatioSRGB :: SRGB -> SRGB -> Double
contrastRatioSRGB c1 c2 =
  contrastRatio (relativeLuminance c1) (relativeLuminance c2)

-- | Minimum contrast ratio required for WCAG compliance
minContrastFor :: WCAGLevel -> TextSize -> Double
minContrastFor AA  NormalText = 4.5
minContrastFor AA  LargeText  = 3.0
minContrastFor AAA NormalText = 7.0
minContrastFor AAA LargeText  = 4.5

-- | Check if a contrast ratio meets WCAG requirements
wcagCompliance :: Double -> WCAGLevel -> TextSize -> Bool
wcagCompliance cr level size = cr >= minContrastFor level size

-- | Check if two colors meet WCAG requirements
meetsWCAG :: SRGB -> SRGB -> WCAGLevel -> TextSize -> Bool
meetsWCAG c1 c2 level size = 
  wcagCompliance (contrastRatioSRGB c1 c2) level size

-- | Adjust lightness of an OKLCH color to achieve target contrast with background
-- 
-- This uses binary search to find the minimal lightness adjustment
-- that achieves the target contrast ratio.
-- 
-- Returns Nothing if the target contrast is impossible to achieve.
adjustLightnessForContrast 
  :: OKLCH      -- ^ Color to adjust
  -> SRGB       -- ^ Background color
  -> Double     -- ^ Target contrast ratio
  -> Bool       -- ^ True = make lighter, False = make darker
  -> Maybe OKLCH
adjustLightnessForContrast color bg targetCR makeLighter =
  let bgLum = relativeLuminance bg
      
      -- Binary search for the right lightness
      search :: Int -> Double -> Double -> Maybe OKLCH
      search iterations lo hi
        | iterations > 50 = Nothing  -- Give up
        | otherwise =
            let mid = (lo + hi) / 2
                candidate = oklchWithLightness mid color
                candidateSrgb = oklchToSrgb candidate
                candidateLum = relativeLuminance candidateSrgb
                cr = contrastRatio candidateLum bgLum
            in if abs (cr - targetCR) < 0.01
               then Just candidate
               else if cr < targetCR
                    then if makeLighter
                         then search (iterations + 1) mid hi
                         else search (iterations + 1) lo mid
                    else if makeLighter
                         then search (iterations + 1) lo mid
                         else search (iterations + 1) mid hi
      
      startL = unUnit (oklchL color)
  in if makeLighter
     then search 0 startL 1.0
     else search 0 0.0 startL
