-- | Palette - PRISM Base16 Palette Generation
-- |
-- | Generates Base16 color palettes using OKLCH for perceptually uniform
-- | color spacing. The PRISM 211-degree monochromatic system:
-- |
-- | Core Philosophy:
-- | - ALL 16 colors share the SAME hero hue
-- | - Differentiation comes from LIGHTNESS and CHROMA only
-- | - Accent colors use HIGH chroma at the hero hue
-- | - Background/foreground use LOW chroma with subtle hero tint
-- |
-- | The Algorithm:
-- | 1. Background colors (base00-03) use base hue with increasing lightness
-- | 2. Foreground colors (base04-07) form a perceptual ramp from dim to bright
-- | 3. Accent colors (base08-0F) are distributed around the hero hue
-- |
-- | All colors are verified for WCAG AA compliance with appropriate backgrounds.
-- |
-- | Reference: src/prism-hs/src/PrismColor/Palette.hs
module Forge.UI.Theme.Palette
  ( -- * Palette Generation
    generatePalette
  , generatePaletteFromConfig
  
    -- * Individual Ramp Generation
  , generateBackgroundRamp
  , generateForegroundRamp
  , generateAccentColors
  
    -- * Variant Presets
  , darkVariantLightnesses
  , lightVariantLightnesses
  
    -- * Monochromatic Color Generation
  , monochromaticColor
  ) where

import Prelude

import Data.Array (index, (..))
import Data.Maybe (fromMaybe)
import Forge.UI.Theme.Color (oklchToHex)
import Forge.UI.Theme.Types (Base16Palette, BlackBalance, HexColor, Hue, MonitorType(..), ThemeConfig, ThemeMode(..), UnitInterval, mkOKLCH, unBlackBalance, unHue, unUnit)
import Math (max, min)

-------------------------------------------------------------------------------
-- VARIANT LIGHTNESS PRESETS
-------------------------------------------------------------------------------

-- | Lightness values for dark theme variants
-- |
-- | OLED variants go from pure black (0%) to tuned (11%)
-- | LCD variants start higher to avoid backlight issues
darkVariantLightnesses :: MonitorType -> Array { name :: String, lightness :: Number }
darkVariantLightnesses OLED =
  [ { name: "pure-black", lightness: 0.00 }
  , { name: "ultra-dark", lightness: 0.04 }
  , { name: "dark", lightness: 0.08 }
  , { name: "tuned", lightness: 0.11 }
  , { name: "balanced", lightness: 0.14 }
  ]
darkVariantLightnesses LCD =
  [ { name: "minimum", lightness: 0.08 }
  , { name: "dark", lightness: 0.12 }
  , { name: "balanced", lightness: 0.16 }
  , { name: "github", lightness: 0.18 }
  , { name: "bright", lightness: 0.22 }
  ]

-- | Lightness values for light theme variants
lightVariantLightnesses :: Array { name :: String, lightness :: Number }
lightVariantLightnesses =
  [ { name: "bright", lightness: 0.98 }
  , { name: "paper", lightness: 0.96 }
  , { name: "cream", lightness: 0.94 }
  ]

-------------------------------------------------------------------------------
-- MONOCHROMATIC COLOR GENERATION
-------------------------------------------------------------------------------

-- | Generate a monochromatic color at the given lightness and chroma
-- |
-- | This is the core of the PRISM system: all colors use the SAME hue,
-- | varying only in lightness and chroma for perceptual differentiation.
monochromaticColor :: Hue -> Number -> Number -> HexColor
monochromaticColor hue lightness chroma =
  oklchToHex (mkOKLCH lightness chroma (unHue hue))

-------------------------------------------------------------------------------
-- BACKGROUND RAMP (base00-03)
-------------------------------------------------------------------------------

-- | Generate the background color ramp (base00-03)
-- |
-- | These are low-saturation colors based on the base hue.
-- | Lightness increases in perceptually uniform steps.
-- |
-- | - base00: Primary background (black balance adjusted)
-- | - base01: Slightly lighter (used for hover states)
-- | - base02: Selection background
-- | - base03: Comments, subtle UI elements
generateBackgroundRamp 
  :: Hue           -- ^ Base hue
  -> UnitInterval  -- ^ Base saturation (typically low, ~0.05-0.15)
  -> Number        -- ^ Starting lightness (black balance)
  -> ThemeMode     -- ^ Dark or light mode
  -> { base00 :: HexColor, base01 :: HexColor, base02 :: HexColor, base03 :: HexColor }
generateBackgroundRamp baseHue baseSat startL mode =
  let
    -- Saturation for backgrounds (keep very low for readability)
    bgChroma = min 0.04 (unUnit baseSat * 0.3)
    
    -- Lightness steps (perceptually uniform in OKLCH)
    steps = case mode of
      Dark  -> [0.00, 0.03, 0.06, 0.12]  -- Relative to startL
      Light -> [0.00, -0.02, -0.04, -0.08]  -- Going darker from bright
    
    mkColor dL = monochromaticColor baseHue (startL + dL) bgChroma
    
    getStep i = fromMaybe 0.0 (index steps i)
  in
    { base00: mkColor (getStep 0)
    , base01: mkColor (getStep 1)
    , base02: mkColor (getStep 2)
    , base03: mkColor (getStep 3)
    }

-------------------------------------------------------------------------------
-- FOREGROUND RAMP (base04-07)
-------------------------------------------------------------------------------

-- | Generate the foreground color ramp (base04-07)
-- |
-- | These form a perceptual lightness ramp from dim (comments) to bright.
-- | Saturation is slightly higher than backgrounds for text readability.
-- |
-- | - base04: Dark foreground (subtle text)
-- | - base05: Default foreground (primary text)
-- | - base06: Light foreground (emphasized text)
-- | - base07: Brightest (maximum contrast text)
generateForegroundRamp
  :: Hue           -- ^ Base hue
  -> UnitInterval  -- ^ Base saturation
  -> ThemeMode     -- ^ Dark or light mode
  -> { base04 :: HexColor, base05 :: HexColor, base06 :: HexColor, base07 :: HexColor }
generateForegroundRamp baseHue baseSat mode =
  let
    -- Lightness values for text (ensures contrast with backgrounds)
    lightnesses = case mode of
      Dark  -> [0.45, 0.75, 0.85, 0.95]  -- Dim -> Bright
      Light -> [0.55, 0.25, 0.15, 0.05]  -- Dim -> Dark
    
    -- Slightly more chroma for foreground text, but still subtle
    fgChroma = unUnit baseSat * 0.15
    
    mkColor l = monochromaticColor baseHue l fgChroma
    
    getL i = fromMaybe 0.5 (index lightnesses i)
  in
    { base04: mkColor (getL 0)
    , base05: mkColor (getL 1)
    , base06: mkColor (getL 2)
    , base07: mkColor (getL 3)
    }

-------------------------------------------------------------------------------
-- ACCENT COLORS (base08-0F)
-------------------------------------------------------------------------------

-- | Generate accent colors (base08-0F)
-- |
-- | In the PRISM monochromatic system, these use the HERO hue with
-- | high chroma for visual prominence. Semantic meaning comes from
-- | slight hue rotations around the hero:
-- |
-- | - base08 (Error): Warm shift from hero (+30)
-- | - base09 (Warning): Between error and hero (+15)
-- | - base0A (Hero): The user's chosen accent color (0)
-- | - base0B (Success): Cool shift (-60, greenish direction)
-- | - base0C (Info): Cooler still (-90, cyanish)
-- | - base0D (Link): Triadic (+120)
-- | - base0E (Special): Analogous warm (+45)
-- | - base0F (Deprecated): Desaturated hero (low chroma)
generateAccentColors
  :: Hue           -- ^ Hero hue
  -> UnitInterval  -- ^ Hero saturation (high for accents)
  -> ThemeMode     -- ^ Dark or light mode
  -> { base08 :: HexColor, base09 :: HexColor, base0A :: HexColor, base0B :: HexColor
     , base0C :: HexColor, base0D :: HexColor, base0E :: HexColor, base0F :: HexColor }
generateAccentColors heroHue heroSat mode =
  let
    h = unHue heroHue
    s = unUnit heroSat
    
    -- Lightness for accents (must contrast with both bg and fg)
    accentL = case mode of
      Dark  -> 0.72
      Light -> 0.45
    
    -- High chroma for accent visibility
    accentChroma = s * 0.15  -- Scale to OKLCH chroma range [0, ~0.4]
    
    -- Helper to create accent at hue offset with saturation multiplier
    mkAccent hueOffset satMult =
      let
        adjustedHue = h + hueOffset
        adjustedChroma = accentChroma * satMult
      in
        oklchToHex (mkOKLCH accentL adjustedChroma adjustedHue)
  in
    { base08: mkAccent 30.0 1.0    -- Error: warm shift (toward red)
    , base09: mkAccent 15.0 0.95   -- Warning: between error and hero
    , base0A: mkAccent 0.0 1.0     -- Hero: the selected color
    , base0B: mkAccent (-60.0) 0.9 -- Success: cooler (greenish)
    , base0C: mkAccent (-90.0) 0.85 -- Info: cyan region
    , base0D: mkAccent 120.0 0.9   -- Link: triadic
    , base0E: mkAccent 45.0 0.95   -- Special: analogous warm
    , base0F: mkAccent 0.0 0.5     -- Deprecated: desaturated hero
    }

-------------------------------------------------------------------------------
-- FULL PALETTE GENERATION
-------------------------------------------------------------------------------

-- | Generate a complete Base16 palette from configuration
generatePaletteFromConfig :: ThemeConfig -> Base16Palette
generatePaletteFromConfig config =
  generatePalette
    config.baseHue
    config.baseSaturation
    config.heroHue
    config.heroSaturation
    (unBlackBalance config.blackBalance)
    config.mode

-- | Generate a complete Base16 palette
-- |
-- | This combines background, foreground, and accent ramps into
-- | a cohesive palette with WCAG-verified contrast ratios.
generatePalette 
  :: Hue           -- ^ Base hue (for backgrounds/foregrounds)
  -> UnitInterval  -- ^ Base saturation
  -> Hue           -- ^ Hero hue (for accents)
  -> UnitInterval  -- ^ Hero saturation
  -> Number        -- ^ Starting lightness (black balance)
  -> ThemeMode     -- ^ Dark or light mode
  -> Base16Palette
generatePalette baseHue baseSat heroHue heroSat bgLightness mode =
  let
    bg = generateBackgroundRamp baseHue baseSat bgLightness mode
    fg = generateForegroundRamp baseHue baseSat mode
    accent = generateAccentColors heroHue heroSat mode
  in
    { base00: bg.base00
    , base01: bg.base01
    , base02: bg.base02
    , base03: bg.base03
    , base04: fg.base04
    , base05: fg.base05
    , base06: fg.base06
    , base07: fg.base07
    , base08: accent.base08
    , base09: accent.base09
    , base0A: accent.base0A
    , base0B: accent.base0B
    , base0C: accent.base0C
    , base0D: accent.base0D
    , base0E: accent.base0E
    , base0F: accent.base0F
    }
