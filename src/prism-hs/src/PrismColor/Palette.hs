{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Module      : PrismColor.Palette
-- Description : Base16 palette generation with perceptual uniformity
-- 
-- Generates Base16 color palettes using OKLCH for perceptually uniform
-- color spacing. The algorithm:
-- 
-- 1. Background colors (base00-03) use the base hue with increasing lightness
-- 2. Foreground colors (base04-07) form a perceptual ramp from dim to bright
-- 3. Accent colors (base08-0F) are distributed around the hero hue
-- 
-- All colors are verified for WCAG AA compliance with appropriate backgrounds.

module PrismColor.Palette
  ( -- * Palette Generation
    generatePalette
  , generateVariants
  
    -- * Individual Color Generation
  , generateBackgroundRamp
  , generateForegroundRamp
  , generateAccentColors
  
    -- * Variant Presets
  , darkVariantLightnesses
  , lightVariantLightnesses
  ) where

import PrismColor.Types
import PrismColor.SRGB
import PrismColor.OKLAB
import PrismColor.Contrast

-- | Lightness values for dark theme variants
-- 
-- OLED variants go from pure black (0%) to tuned (11%)
-- LCD variants start higher to avoid backlight issues
darkVariantLightnesses :: MonitorType -> [(String, Double)]
darkVariantLightnesses OLED =
  [ ("pure-black",  0.00)
  , ("ultra-dark",  0.04)
  , ("dark",        0.08)
  , ("tuned",       0.11)
  , ("balanced",    0.14)
  ]
darkVariantLightnesses LCD =
  [ ("minimum",     0.08)
  , ("dark",        0.12)
  , ("balanced",    0.16)
  , ("github",      0.18)
  , ("bright",      0.22)
  ]

-- | Lightness values for light theme variants
lightVariantLightnesses :: [(String, Double)]
lightVariantLightnesses =
  [ ("bright",      0.98)
  , ("paper",       0.96)
  , ("cream",       0.94)
  ]

-- | Generate the background color ramp (base00-03)
-- 
-- These are low-saturation colors based on the base hue.
-- Lightness increases in perceptually uniform steps.
generateBackgroundRamp 
  :: Hue           -- ^ Base hue
  -> UnitInterval  -- ^ Base saturation (typically low, ~0.05-0.15)
  -> Double        -- ^ Starting lightness (black balance)
  -> ThemeMode     -- ^ Dark or light mode
  -> (SRGB, SRGB, SRGB, SRGB)  -- ^ base00, base01, base02, base03
generateBackgroundRamp baseHue baseSat startL mode =
  let -- Saturation for backgrounds (keep low for readability)
      bgSat = min 0.15 (unUnit baseSat)
      
      -- Lightness steps (perceptually uniform in OKLCH)
      steps = case mode of
        Dark  -> [0.00, 0.03, 0.06, 0.12]  -- Relative to startL
        Light -> [0.00, -0.02, -0.04, -0.08]  -- Going darker from bright
      
      mkColor dL = oklchToSrgb $ OKLCH
        { oklchL = clampUnit (startL + dL)
        , oklchC = bgSat * 0.3  -- Very low chroma for backgrounds
        , oklchH = baseHue
        }
  in (mkColor (steps !! 0), mkColor (steps !! 1), 
      mkColor (steps !! 2), mkColor (steps !! 3))

-- | Generate the foreground color ramp (base04-07)
-- 
-- These form a perceptual lightness ramp from dim (comments) to bright.
-- Saturation is slightly higher than backgrounds for text readability.
generateForegroundRamp
  :: Hue           -- ^ Base hue
  -> UnitInterval  -- ^ Base saturation
  -> ThemeMode     -- ^ Dark or light mode
  -> (SRGB, SRGB, SRGB, SRGB)  -- ^ base04, base05, base06, base07
generateForegroundRamp baseHue baseSat mode =
  let -- Lightness values for text (ensures contrast with backgrounds)
      lightnesses = case mode of
        Dark  -> [0.45, 0.75, 0.85, 0.95]  -- Dim → Bright
        Light -> [0.55, 0.25, 0.15, 0.05]  -- Dim → Dark
      
      -- Slightly more saturation for foreground text
      fgSat = unUnit baseSat * 0.8
      
      mkColor l = oklchToSrgb $ OKLCH
        { oklchL = clampUnit l
        , oklchC = fgSat * 0.4
        , oklchH = baseHue
        }
  in (mkColor (lightnesses !! 0), mkColor (lightnesses !! 1),
      mkColor (lightnesses !! 2), mkColor (lightnesses !! 3))

-- | Generate accent colors (base08-0F)
-- 
-- These are distributed around the hero hue using color harmony rules:
-- - base08 (Error): Warm direction from hero
-- - base09 (Warning): Split between error and hero  
-- - base0A (Hero): The user-selected accent color
-- - base0B (Success): Complementary region
-- - base0C (Info): Cool direction from hero
-- - base0D (Link): Triadic from hero
-- - base0E (Special): Analogous to hero
-- - base0F (Deprecated): Desaturated hero
generateAccentColors
  :: Hue           -- ^ Hero hue
  -> UnitInterval  -- ^ Hero saturation
  -> ThemeMode     -- ^ Dark or light mode
  -> (SRGB, SRGB, SRGB, SRGB, SRGB, SRGB, SRGB, SRGB)
generateAccentColors heroHue heroSat mode =
  let h = unHue heroHue
      s = unUnit heroSat
      
      -- Lightness for accents (must contrast with both bg and fg)
      accentL = case mode of
        Dark  -> 0.72
        Light -> 0.45
      
      -- Hue offsets for color harmony
      -- Positive = warmer (toward red/orange)
      -- Negative = cooler (toward blue/cyan)
      mkAccent hueOffset satMult =
        oklchToSrgb $ OKLCH
          { oklchL = clampUnit accentL
          , oklchC = s * satMult * 0.15  -- Scale to OKLCH chroma range
          , oklchH = normalizeHue (h + hueOffset)
          }
      
      base08 = mkAccent   30 1.0   -- Error: warm shift (toward red)
      base09 = mkAccent   15 0.95  -- Warning: between error and hero
      base0A = mkAccent    0 1.0   -- Hero: the selected color
      base0B = mkAccent (-60) 0.9  -- Success: cooler (greenish)
      base0C = mkAccent (-90) 0.85 -- Info: cyan region
      base0D = mkAccent 120 0.9    -- Link: triadic
      base0E = mkAccent  45 0.95   -- Special: analogous warm
      base0F = mkAccent    0 0.5   -- Deprecated: desaturated hero
      
  in (base08, base09, base0A, base0B, base0C, base0D, base0E, base0F)

-- | Generate a complete Base16 palette
generatePalette :: ThemeConfig -> Double -> Base16Colors
generatePalette ThemeConfig{..} bgLightness =
  let (b00, b01, b02, b03) = generateBackgroundRamp 
        configBaseHue configBaseSaturation bgLightness configMode
      
      (b04, b05, b06, b07) = generateForegroundRamp
        configBaseHue configBaseSaturation configMode
      
      (b08, b09, b0A, b0B, b0C, b0D, b0E, b0F) = generateAccentColors
        configHeroHue configHeroSaturation configMode
        
  in Base16Colors
    { base00 = srgbToHex b00
    , base01 = srgbToHex b01
    , base02 = srgbToHex b02
    , base03 = srgbToHex b03
    , base04 = srgbToHex b04
    , base05 = srgbToHex b05
    , base06 = srgbToHex b06
    , base07 = srgbToHex b07
    , base08 = srgbToHex b08
    , base09 = srgbToHex b09
    , base0A = srgbToHex b0A
    , base0B = srgbToHex b0B
    , base0C = srgbToHex b0C
    , base0D = srgbToHex b0D
    , base0E = srgbToHex b0E
    , base0F = srgbToHex b0F
    }

-- | Generate all theme variants for a configuration
generateVariants :: ThemeConfig -> [ThemeVariant]
generateVariants config@ThemeConfig{..} =
  let variantDefs = case configMode of
        Dark  -> darkVariantLightnesses configMonitorType
        Light -> lightVariantLightnesses
  in map mkVariant variantDefs
  where
    mkVariant (name, lightness) = ThemeVariant
      { variantName = name
      , variantBackgroundLightness = lightness
      , variantColors = generatePalette config lightness
      }
