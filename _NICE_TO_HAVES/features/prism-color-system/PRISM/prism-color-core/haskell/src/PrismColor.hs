-- |
-- Module      : PrismColor
-- Description : Formally verified color science for theme generation
-- Copyright   : (c) Prism Compositor, 2024
-- License     : MIT
-- 
-- This library provides perceptually uniform color manipulation using
-- OKLAB/OKLCH color spaces, with mathematical foundations proven in Lean4.
-- 
-- = Quick Start
-- 
-- @
-- import PrismColor
-- 
-- -- Generate themes from a configuration
-- let config = ThemeConfig
--       { configBaseHue = normalizeHue 211
--       , configBaseSaturation = clampUnit 0.12
--       , configHeroHue = normalizeHue 211
--       , configHeroSaturation = clampUnit 1.0
--       , configMonitorType = OLED
--       , configBlackBalance = defaultBlackBalance OLED
--       , configMode = Dark
--       }
-- 
-- let variants = generateVariants config
-- @
-- 
-- = Color Spaces
-- 
-- The library supports these color spaces:
-- 
-- * 'SRGB' - Standard RGB (what monitors display)
-- * 'LinearRGB' - Linear light RGB (for color math)
-- * 'XYZ' - CIE XYZ (device-independent)
-- * 'OKLAB' - Perceptually uniform Lab space
-- * 'OKLCH' - Cylindrical OKLAB (Lightness, Chroma, Hue)
-- 
-- Use OKLCH for palette generation - it provides perceptually uniform
-- lightness and hue interpolation.
-- 
-- = WCAG Compliance
-- 
-- The 'PrismColor.Contrast' module provides WCAG 2.1 contrast calculations.
-- All generated palettes are verified to meet AA standards.

module PrismColor
  ( -- * Re-exports
    module PrismColor.Types
  , module PrismColor.SRGB
  , module PrismColor.OKLAB
  , module PrismColor.Contrast
  , module PrismColor.Palette
  , module PrismColor.FFI
  ) where

import PrismColor.Types
import PrismColor.SRGB
import PrismColor.OKLAB
import PrismColor.Contrast
import PrismColor.Palette
import PrismColor.FFI
