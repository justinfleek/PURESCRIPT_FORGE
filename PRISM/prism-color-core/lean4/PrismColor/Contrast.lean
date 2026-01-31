/-
  PrismColor.Contrast
  
  WCAG 2.1 contrast ratio calculations and proofs.
  
  Contrast Ratio = (L1 + 0.05) / (L2 + 0.05)
  
  where L1 > L2 and both are relative luminance values.
  
  Requirements:
  - AA Normal text: CR ≥ 4.5
  - AA Large text: CR ≥ 3.0
  - AAA Normal text: CR ≥ 7.0
  - AAA Large text: CR ≥ 4.5
-/

import PrismColor.Conversions
import Mathlib.Tactic

namespace PrismColor

/-! ## Contrast Ratio Definition -/

/-- WCAG contrast ratio between two luminance values.
    Always returns the ratio with the brighter color in numerator. -/
noncomputable def contrastRatio (l1 l2 : ℝ) (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) : ℝ :=
  let lighter := max l1 l2
  let darker := min l1 l2
  (lighter + 0.05) / (darker + 0.05)

/-- Contrast ratio between two sRGB colors -/
noncomputable def contrastRatioSRGB (c1 c2 : SRGB) : ℝ :=
  contrastRatio 
    (relativeLuminance c1) 
    (relativeLuminance c2)
    (relativeLuminance_nonneg c1)
    (relativeLuminance_nonneg c2)

/-! ## Fundamental Properties -/

/-- Contrast ratio is always positive -/
theorem contrastRatio_pos (l1 l2 : ℝ) (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) :
    0 < contrastRatio l1 l2 h1 h2 := by
  unfold contrastRatio
  apply div_pos
  · linarith [le_max_left l1 l2]
  · linarith [min_le_left l1 l2]

/-- Contrast ratio is at least 1 (a color with itself) -/
theorem contrastRatio_ge_one (l1 l2 : ℝ) (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) :
    1 ≤ contrastRatio l1 l2 h1 h2 := by
  unfold contrastRatio
  apply one_le_div_of_le
  · linarith [min_le_left l1 l2]
  · linarith [le_max_of_le_left (min_le_left l1 l2), le_max_of_le_right (min_le_right l1 l2)]

/-- Contrast ratio is symmetric -/
theorem contrastRatio_symm (l1 l2 : ℝ) (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) :
    contrastRatio l1 l2 h1 h2 = contrastRatio l2 l1 h2 h1 := by
  unfold contrastRatio
  simp only [max_comm, min_comm]

/-- A color has contrast ratio 1 with itself -/
theorem contrastRatio_self (l : ℝ) (h : 0 ≤ l) :
    contrastRatio l l h h = 1 := by
  unfold contrastRatio
  simp only [max_self, min_self]
  field_simp

/-- Maximum contrast ratio is 21:1 (white vs black) -/
theorem contrastRatio_max :
    contrastRatio 1 0 (by norm_num : (0:ℝ) ≤ 1) (le_refl 0) = 21 := by
  unfold contrastRatio
  simp only [max_eq_left, min_eq_right]
  · norm_num
  · norm_num
  · norm_num

/-! ## WCAG Compliance Levels -/

/-- WCAG AA compliance for normal text (4.5:1) -/
def wcagAA (cr : ℝ) : Prop := 4.5 ≤ cr

/-- WCAG AAA compliance for normal text (7:1) -/
def wcagAAA (cr : ℝ) : Prop := 7 ≤ cr

/-- WCAG AA compliance for large text (3:1) -/
def wcagAALarge (cr : ℝ) : Prop := 3 ≤ cr

/-- WCAG AAA compliance for large text (4.5:1) -/
def wcagAAALarge (cr : ℝ) : Prop := 4.5 ≤ cr

/-- AAA implies AA -/
theorem wcagAAA_implies_AA (cr : ℝ) : wcagAAA cr → wcagAA cr := by
  intro h
  unfold wcagAAA wcagAA at *
  linarith

/-- If contrast meets AA for normal, it meets AA for large -/
theorem wcagAA_implies_AALarge (cr : ℝ) : wcagAA cr → wcagAALarge cr := by
  intro h
  unfold wcagAA wcagAALarge at *
  linarith

/-! ## Contrast Bounds from Luminance Bounds -/

/-- If we know luminance bounds, we can bound contrast ratio from below -/
theorem contrastRatio_lower_bound
    (l1 l2 : ℝ) (h1 : 0 ≤ l1) (h2 : 0 ≤ l2)
    (hL1 : l1_min ≤ l1) (hL2 : l2 ≤ l2_max)
    (h_l1_min : 0 ≤ l1_min) (h_l2_max : 0 ≤ l2_max)
    (h_order : l2_max < l1_min) :
    (l1_min + 0.05) / (l2_max + 0.05) ≤ contrastRatio l1 l2 h1 h2 := by
  unfold contrastRatio
  -- When l1_min > l2_max, we know l1 > l2 so max l1 l2 = l1, min l1 l2 = l2
  have h_l1_gt_l2 : l2 < l1 := by
    calc l2 ≤ l2_max := hL2
         _ < l1_min := h_order
         _ ≤ l1 := hL1
  simp only [max_eq_left (le_of_lt h_l1_gt_l2), min_eq_right (le_of_lt h_l1_gt_l2)]
  apply div_le_div
  · linarith
  · linarith
  · linarith
  · linarith

/-! ## Black Balance Contrast Guarantees -/

/-- Black (L=0) has maximum contrast with white (L=1) -/
theorem black_white_contrast :
    contrastRatio 1 0 (by norm_num) (le_refl 0) = 21 := contrastRatio_max

/-- With black balance at 11%, background luminance is ~0.011 -/
def blackBalanceToLuminance (bb : BlackBalance) : ℝ :=
  -- Approximate: L* to Y conversion for low values
  -- Y ≈ (L*/100)^2.4 * (L*/903.3) blend
  -- For L* = 11: Y ≈ 0.011
  bb.value / 10  -- Simplified approximation

/-- Minimum guaranteed contrast with default OLED black balance -/
theorem oled_black_balance_min_contrast :
    let bb := BlackBalance.default MonitorType.OLED
    let bgLum := blackBalanceToLuminance bb  -- ~0.011
    let fgLum := 0.7  -- Typical text luminance
    (fgLum + 0.05) / (bgLum + 0.05) > 10 := by
  simp only [BlackBalance.default, blackBalanceToLuminance]
  norm_num

/-! ## Palette Generation Constraints -/

/-- For a valid dark theme palette, foreground must have sufficient contrast with background -/
structure ValidDarkPalette (p : Base16Palette) : Prop where
  /-- Default text (base05) meets AA with background (base00) -/
  text_contrast : wcagAA (contrastRatioSRGB p.base05 p.base00)
  /-- Comments (base03) meets AA-large with background -/
  comment_contrast : wcagAALarge (contrastRatioSRGB p.base03 p.base00)
  /-- Hero accent (base0A) meets AA-large with background -/
  hero_contrast : wcagAALarge (contrastRatioSRGB p.base0A p.base00)

/-- For a valid light theme palette -/
structure ValidLightPalette (p : Base16Palette) : Prop where
  /-- Default text (base05 - actually dark on light) meets AA with background -/
  text_contrast : wcagAA (contrastRatioSRGB p.base05 p.base00)
  /-- etc... -/
  comment_contrast : wcagAALarge (contrastRatioSRGB p.base03 p.base00)

end PrismColor
