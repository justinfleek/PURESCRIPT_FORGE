/-
  PrismColor.Basic
  
  Core types for color representation with bounded values.
  All color components are represented as rationals in [0,1].
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace PrismColor

/-- A value bounded in the unit interval [0,1] -/
structure UnitInterval where
  val : ℝ
  lower : 0 ≤ val
  upper : val ≤ 1

instance : Inhabited UnitInterval where
  default := ⟨0, le_refl 0, zero_le_one⟩

/-- Smart constructor for UnitInterval with clamping -/
def UnitInterval.clamp (x : ℝ) : UnitInterval :=
  ⟨max 0 (min x 1), 
   le_max_left 0 _, 
   max_le (min_le_right x 1) (min_le_right x 1)⟩

/-- Hue angle in degrees [0, 360) -/
structure Hue where
  degrees : ℝ
  lower : 0 ≤ degrees
  upper : degrees < 360

/-- Normalize any angle to [0, 360) using modular arithmetic -/
def Hue.normalize (x : ℝ) : Hue :=
  let normalized := x - 360 * ⌊x / 360⌋
  ⟨normalized, 
   by -- Prove 0 ≤ normalized
      simp only [normalized]
      have hfloor : ⌊x / 360⌋ ≤ x / 360 := Int.floor_le (x / 360)
      have h360 : (360 : ℝ) > 0 := by norm_num
      have hmul : 360 * ↑⌊x / 360⌋ ≤ 360 * (x / 360) := by
        apply mul_le_mul_of_nonneg_left hfloor (le_of_lt h360)
      simp only [mul_div_cancel₀ 360 (ne_of_gt h360)] at hmul
      linarith,
   by -- Prove normalized < 360
      simp only [normalized]
      have hfloor : x / 360 < ⌊x / 360⌋ + 1 := Int.lt_floor_add_one (x / 360)
      have h360 : (360 : ℝ) > 0 := by norm_num
      have hmul : 360 * (x / 360) < 360 * (↑⌊x / 360⌋ + 1) := by
        apply mul_lt_mul_of_pos_left hfloor h360
      simp only [mul_div_cancel₀ 360 (ne_of_gt h360)] at hmul
      linarith⟩

/-- sRGB color space - gamma-corrected device color -/
structure SRGB where
  r : UnitInterval
  g : UnitInterval
  b : UnitInterval

/-- Linear RGB - physical light intensity, no gamma -/
structure LinearRGB where
  r : UnitInterval
  g : UnitInterval
  b : UnitInterval

/-- CIE XYZ color space with D65 white point -/
structure XYZ where
  x : ℝ
  y : ℝ  -- Y is luminance
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z

/-- OKLAB perceptually uniform color space -/
structure OKLAB where
  l : UnitInterval  -- Lightness
  a : ℝ             -- Green-Red axis (unbounded but typically [-0.4, 0.4])
  b : ℝ             -- Blue-Yellow axis

/-- OKLCH cylindrical form of OKLAB -/
structure OKLCH where
  l : UnitInterval  -- Lightness
  c : ℝ             -- Chroma (≥ 0)
  h : Hue           -- Hue angle
  c_nonneg : 0 ≤ c

/-- Monitor type affects optimal black balance -/
inductive MonitorType
  | OLED  -- Optimal black balance ~11%
  | LCD   -- Optimal black balance ~16%

/-- Theme mode -/
inductive ThemeMode
  | Dark
  | Light

/-- Black balance as a bounded percentage -/
structure BlackBalance where
  value : ℝ
  lower : 0 ≤ value
  upper : value ≤ 0.20

def BlackBalance.default (m : MonitorType) : BlackBalance :=
  match m with
  | .OLED => ⟨0.11, by norm_num, by norm_num⟩
  | .LCD  => ⟨0.16, by norm_num, by norm_num⟩

/-- Base16 color scheme - 16 semantic color slots -/
structure Base16Palette where
  base00 : SRGB  -- Background
  base01 : SRGB  -- Lighter background
  base02 : SRGB  -- Selection
  base03 : SRGB  -- Comments
  base04 : SRGB  -- Dark foreground
  base05 : SRGB  -- Default foreground
  base06 : SRGB  -- Light foreground
  base07 : SRGB  -- Brightest
  base08 : SRGB  -- Error/Red
  base09 : SRGB  -- Warning/Orange
  base0A : SRGB  -- Hero accent
  base0B : SRGB  -- Success/Green
  base0C : SRGB  -- Info/Cyan
  base0D : SRGB  -- Link/Blue
  base0E : SRGB  -- Special/Purple
  base0F : SRGB  -- Deprecated

/-- Theme configuration -/
structure ThemeConfig where
  baseHue : Hue
  baseSaturation : UnitInterval
  heroHue : Hue
  heroSaturation : UnitInterval
  monitorType : MonitorType
  blackBalance : BlackBalance
  mode : ThemeMode

/-- Generated theme variant -/
structure ThemeVariant where
  name : String
  backgroundLightness : UnitInterval
  palette : Base16Palette

end PrismColor
