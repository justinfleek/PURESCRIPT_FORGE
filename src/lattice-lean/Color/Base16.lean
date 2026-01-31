-- |
-- Module      : Color.Base16
-- Description : Base16 color theme generator using 211° hero hue
--
-- Generates base16 color schemes with HSL(211° ...) hero hue lock
-- Based on ono-sendai color scheme patterns
--

import Color.Color
import Mathlib.Data.List.Basic

-- ============================================================================
-- BASE16 COLOR STRUCTURE
-- ============================================================================

-- | Base16 color palette (16 colors)
structure Base16Palette where
  base00 : RGB  -- Background (darkest)
  base01 : RGB  -- Lighter background
  base02 : RGB  -- Selection background
  base03 : RGB  -- Comments/inactive
  base04 : RGB  -- Dark foreground
  base05 : RGB  -- Default foreground
  base06 : RGB  -- Light foreground
  base07 : RGB  -- Lightest background
  base08 : RGB  -- Variables/errors
  base09 : RGB  -- Integers
  base0A : RGB  -- Classes (HERO: 211°)
  base0B : RGB  -- Strings
  base0C : RGB  -- Support/functions
  base0D : RGB  -- Functions/links
  base0E : RGB  -- Keywords
  base0F : RGB  -- Deprecated/markers
  deriving Repr

-- ============================================================================
-- BASE16 THEME GENERATOR
-- ============================================================================

-- | Helper to create Saturation with proof
def mkSaturation (v : ℝ) (h : 0 ≤ v ∧ v ≤ 1) : Saturation :=
  { value := v, s_0_le := h.1, s_le_1 := h.2 }

-- | Helper to create Lightness with proof
def mkLightness (v : ℝ) (h : 0 ≤ v ∧ v ≤ 1) : Lightness :=
  { value := v, l_0_le := h.1, l_le_1 := h.2 }

-- | Create Hue at 201° (cool shift from hero)
def coolHue201 : Hue :=
  Color.degreesToHue 201

-- | Generate accent colors with 211° hero hue
-- Creates systematic relationships to hero blue
def generateAccentColors : List HSL :=
  [
    -- base08: Ice blue (shifted cool, high luminance) HSL(201° 100% 86%)
    { h := coolHue201
      s := mkSaturation 1.0 ⟨by norm_num, by norm_num⟩
      l := mkLightness 0.86 ⟨by norm_num, by norm_num⟩
    }
    -- base09: Sky blue (same hue, darker) HSL(201° 100% 75%)
    { h := coolHue201
      s := mkSaturation 1.0 ⟨by norm_num, by norm_num⟩
      l := mkLightness 0.75 ⟨by norm_num, by norm_num⟩
    }
    -- base0A: HERO Electric blue HSL(211° 100% 66%) - #54aeff
    { h := Color.heroHue
      s := mkSaturation 1.0 ⟨by norm_num, by norm_num⟩
      l := mkLightness 0.66 ⟨by norm_num, by norm_num⟩
    }
    -- base0B: Deep blue (same hue, darker) HSL(211° 100% 57%)
    { h := Color.heroHue
      s := mkSaturation 1.0 ⟨by norm_num, by norm_num⟩
      l := mkLightness 0.57 ⟨by norm_num, by norm_num⟩
    }
    -- base0C: Matrix blue (desaturated) HSL(211° 94% 45%)
    { h := Color.heroHue
      s := mkSaturation 0.94 ⟨by norm_num, by norm_num⟩
      l := mkLightness 0.45 ⟨by norm_num, by norm_num⟩
    }
    -- base0D: Link blue (tiny luminance shift) HSL(211° 100% 65%)
    { h := Color.heroHue
      s := mkSaturation 1.0 ⟨by norm_num, by norm_num⟩
      l := mkLightness 0.65 ⟨by norm_num, by norm_num⟩
    }
    -- base0E: Soft electric (lighter variant) HSL(211° 100% 71%)
    { h := Color.heroHue
      s := mkSaturation 1.0 ⟨by norm_num, by norm_num⟩
      l := mkLightness 0.71 ⟨by norm_num, by norm_num⟩
    }
    -- base0F: Corp blue (desaturated dark) HSL(211° 86% 53%)
    { h := Color.heroHue
      s := mkSaturation 0.86 ⟨by norm_num, by norm_num⟩
      l := mkLightness 0.53 ⟨by norm_num, by norm_num⟩
    }
  ]

-- | Generate base16 palette with 211° hero hue
def generateBase16Theme (backgroundLightness : ℝ) (h_bg : 0 ≤ backgroundLightness ∧ backgroundLightness ≤ 1) : Base16Palette :=
  -- Grayscale ramp (base00-base07) with 211° hue tint
  let base00 := Color.hslWithHeroHue (mkSaturation 0.12 ⟨by norm_num, by norm_num⟩) (mkLightness backgroundLightness h_bg)
  let base01 := Color.hslWithHeroHue (mkSaturation 0.16 ⟨by norm_num, by norm_num⟩) (mkLightness (backgroundLightness + 0.03) ⟨by linarith, by linarith⟩)
  let base02 := Color.hslWithHeroHue (mkSaturation 0.17 ⟨by norm_num, by norm_num⟩) (mkLightness (backgroundLightness + 0.08) ⟨by linarith, by linarith⟩)
  let base03 := Color.hslWithHeroHue (mkSaturation 0.15 ⟨by norm_num, by norm_num⟩) (mkLightness (backgroundLightness + 0.17) ⟨by linarith, by linarith⟩)
  let base04 := Color.hslWithHeroHue (mkSaturation 0.12 ⟨by norm_num, by norm_num⟩) (mkLightness 0.48 ⟨by norm_num, by norm_num⟩)
  let base05 := Color.hslWithHeroHue (mkSaturation 0.28 ⟨by norm_num, by norm_num⟩) (mkLightness 0.81 ⟨by norm_num, by norm_num⟩)
  let base06 := Color.hslWithHeroHue (mkSaturation 0.32 ⟨by norm_num, by norm_num⟩) (mkLightness 0.89 ⟨by norm_num, by norm_num⟩)
  let base07 := Color.hslWithHeroHue (mkSaturation 0.36 ⟨by norm_num, by norm_num⟩) (mkLightness 0.95 ⟨by norm_num, by norm_num⟩)
  let accents := generateAccentColors
  -- Extract accent colors safely using pattern matching
  let base08HSL := match accents with
    | h1 :: _ => h1
    | _ => Color.hslWithHeroHue (mkSaturation 1.0 ⟨by norm_num, by norm_num⟩) (mkLightness 0.86 ⟨by norm_num, by norm_num⟩)
  let base09HSL := match accents with
    | _ :: h2 :: _ => h2
    | _ => Color.hslWithHeroHue (mkSaturation 1.0 ⟨by norm_num, by norm_num⟩) (mkLightness 0.75 ⟨by norm_num, by norm_num⟩)
  let base0AHSL := match accents with
    | _ :: _ :: h3 :: _ => h3
    | _ => Color.hslWithHeroHue (mkSaturation 1.0 ⟨by norm_num, by norm_num⟩) (mkLightness 0.66 ⟨by norm_num, by norm_num⟩)
  let base0BHSL := match accents with
    | _ :: _ :: _ :: h4 :: _ => h4
    | _ => Color.hslWithHeroHue (mkSaturation 1.0 ⟨by norm_num, by norm_num⟩) (mkLightness 0.57 ⟨by norm_num, by norm_num⟩)
  let base0CHSL := match accents with
    | _ :: _ :: _ :: _ :: h5 :: _ => h5
    | _ => Color.hslWithHeroHue (mkSaturation 0.94 ⟨by norm_num, by norm_num⟩) (mkLightness 0.45 ⟨by norm_num, by norm_num⟩)
  let base0DHSL := match accents with
    | _ :: _ :: _ :: _ :: _ :: h6 :: _ => h6
    | _ => Color.hslWithHeroHue (mkSaturation 1.0 ⟨by norm_num, by norm_num⟩) (mkLightness 0.65 ⟨by norm_num, by norm_num⟩)
  let base0EHSL := match accents with
    | _ :: _ :: _ :: _ :: _ :: _ :: h7 :: _ => h7
    | _ => Color.hslWithHeroHue (mkSaturation 1.0 ⟨by norm_num, by norm_num⟩) (mkLightness 0.71 ⟨by norm_num, by norm_num⟩)
  let base0FHSL := match accents with
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: h8 :: _ => h8
    | _ => Color.hslWithHeroHue (mkSaturation 0.86 ⟨by norm_num, by norm_num⟩) (mkLightness 0.53 ⟨by norm_num, by norm_num⟩)
  {
    base00 := hslToRGB base00
    base01 := hslToRGB base01
    base02 := hslToRGB base02
    base03 := hslToRGB base03
    base04 := hslToRGB base04
    base05 := hslToRGB base05
    base06 := hslToRGB base06
    base07 := hslToRGB base07
    base08 := hslToRGB base08HSL
    base09 := hslToRGB base09HSL
    base0A := hslToRGB base0AHSL  -- HERO: #54aeff
    base0B := hslToRGB base0BHSL
    base0C := hslToRGB base0CHSL
    base0D := hslToRGB base0DHSL
    base0E := hslToRGB base0EHSL
    base0F := hslToRGB base0FHSL
  }

-- | Generate ono-sendai tuned theme (L=11% background)
-- HSL(211° 12% 11%) - OLED-safe background
def onoSendaiTuned : Base16Palette :=
  generateBase16Theme 0.11 ⟨by norm_num, by norm_num⟩

-- | Generate ono-sendai github theme (L=16% background)
-- HSL(211° 12% 16%) - GitHub's de-facto default dark mode
def onoSendaiGithub : Base16Palette :=
  generateBase16Theme 0.16 ⟨by norm_num, by norm_num⟩

-- | Generate ono-sendai memphis theme (L=0% background - pure black)
-- HSL(211° 0% 0%) - Pure black
def onoSendaiMemphis : Base16Palette :=
  generateBase16Theme 0.0 ⟨by norm_num, by norm_num⟩

-- | Generate ono-sendai chiba theme (L=4% background)
-- HSL(211° 12% 4%) - Problematic on Samsung panels
def onoSendaiChiba : Base16Palette :=
  generateBase16Theme 0.04 ⟨by norm_num, by norm_num⟩

-- | Generate ono-sendai razorgirl theme (L=8% background)
-- HSL(211° 12% 8%) - Attempt to preserve strokes
def onoSendaiRazorgirl : Base16Palette :=
  generateBase16Theme 0.08 ⟨by norm_num, by norm_num⟩

-- | Generate ono-sendai sprawl theme (L=11% background - best compromise)
-- HSL(211° 12% 11%) - Best compromise
def onoSendaiSprawl : Base16Palette :=
  generateBase16Theme 0.11 ⟨by norm_num, by norm_num⟩
