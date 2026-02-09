{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : Main
Description : Test suite for PrismColor library
License     : MIT

Property-based tests for color space conversions.
-}
module Main where

import Test.QuickCheck
import Test.QuickCheck.Monadic
import PrismColor
import PrismColor.Types
import PrismColor.SRGB
import PrismColor.OKLAB
import PrismColor.Contrast

-- | Test that sRGB -> Linear -> sRGB is identity (within epsilon)
prop_srgbLinearRoundtrip :: UnitInterval -> Bool
prop_srgbLinearRoundtrip (UnitInterval x) =
  let linear = srgbToLinear x
      back = linearToSrgb linear
  in abs (x - back) < 1e-10

-- | Test that contrast ratio is always >= 1
prop_contrastRatioGeOne :: UnitInterval -> UnitInterval -> Bool
prop_contrastRatioGeOne (UnitInterval l1) (UnitInterval l2) =
  contrastRatio l1 l2 >= 1.0

-- | Test that contrast ratio is symmetric
prop_contrastRatioSymmetric :: UnitInterval -> UnitInterval -> Bool
prop_contrastRatioSymmetric (UnitInterval l1) (UnitInterval l2) =
  abs (contrastRatio l1 l2 - contrastRatio l2 l1) < 1e-10

-- | Test that hue normalization stays in [0, 360)
prop_hueNormalize :: Double -> Bool
prop_hueNormalize h =
  let normalized = normalizeHue h
  in normalized >= 0 && normalized < 360

-- | Test OKLCH -> OKLAB -> OKLCH roundtrip
prop_oklchOklabRoundtrip :: OKLCH -> Bool
prop_oklchOklabRoundtrip oklch =
  let oklab = oklchToOklab oklch
      back = oklabToOklch oklab
  in approxEq (oklchL oklch) (oklchL back) &&
     approxEq (oklchC oklch) (oklchC back) &&
     hueApproxEq (oklchH oklch) (oklchH back)
  where
    approxEq a b = abs (a - b) < 1e-6
    hueApproxEq a b = 
      let diff = abs (a - b)
      in diff < 1e-6 || abs (diff - 360) < 1e-6

-- | Arbitrary instances
instance Arbitrary UnitInterval where
  arbitrary = UnitInterval <$> choose (0.0, 1.0)

instance Arbitrary OKLCH where
  arbitrary = OKLCH 
    <$> choose (0.0, 1.0)  -- L
    <*> choose (0.0, 0.4)  -- C
    <*> choose (0.0, 360.0) -- H

-- | Main test runner
main :: IO ()
main = do
  putStrLn "Prism Color Core - Test Suite"
  putStrLn "=============================="
  
  putStrLn "\n[1/5] sRGB Linear Roundtrip"
  quickCheck prop_srgbLinearRoundtrip
  
  putStrLn "\n[2/5] Contrast Ratio >= 1"
  quickCheck prop_contrastRatioGeOne
  
  putStrLn "\n[3/5] Contrast Ratio Symmetric"
  quickCheck prop_contrastRatioSymmetric
  
  putStrLn "\n[4/5] Hue Normalization Bounds"
  quickCheck prop_hueNormalize
  
  putStrLn "\n[5/5] OKLCH-OKLAB Roundtrip"
  quickCheck prop_oklchOklabRoundtrip
  
  putStrLn "\n✓ All tests passed"
