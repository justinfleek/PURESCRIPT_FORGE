# Prism Color Core: Architecture & Gap Analysis

## Executive Summary

The Prism Theme Generator consists of three editor plugins (VSCode, Neovim, Emacs) that currently have **no functional backend**. All three reference a Python→Haskell FFI bridge that doesn't exist. The VSCode version has mock implementations that use perceptually incorrect HSL math.

This document outlines the architecture for a **formally verified color science core** with Lean4 proofs and Haskell/PureScript implementations.

---

## Critical Gaps

### 1. **No Backend Exists**

| Component | Status | Impact |
|-----------|--------|--------|
| `theme_generator_ffi.py` | ❌ Missing | All FFI calls fail |
| `libprism-ffi.so` | ❌ Missing | Native calls fail |
| `generate_theme_variants_ffi` | ❌ Missing | Core function doesn't exist |
| Haskell color library | ❌ Missing | No color math |

### 2. **Perceptually Incorrect Color Math**

The VSCode mock uses raw HSL which is **perceptually non-uniform**:
- HSL L=50% looks different across hues (yellow appears brighter than blue)
- No gamma correction (sRGB transfer function)
- No chromatic adaptation
- Contrast calculations would be wrong

**Required**: OKLCH/OKLAB for perceptual uniformity.

### 3. **No Accessibility Compliance**

Missing:
- WCAG 2.1 contrast ratio calculations (AA: 4.5:1, AAA: 7:1)
- Color blindness simulation (protanopia, deuteranopia, tritanopia)
- Semantic color relationships (error=red only works for some users)

### 4. **No Formal Verification**

Comments reference "Lean4 proofs" but none exist. Critical properties to prove:
- Color space conversions are bijective (roundtrip identity)
- Gamut mapping preserves hue
- Contrast ratios satisfy WCAG bounds
- Black balance stays within valid luminance range

### 5. **Plugin-Specific Gaps**

#### VSCode
- ✅ UI mostly complete
- ❌ Webview code mixed with extension code (architectural debt)
- ❌ No theme installation to VS Code settings
- ❌ No live preview in actual editor

#### Neovim
- ❌ UI is ASCII placeholder only
- ❌ No actual color picker
- ❌ No highlight group application
- ❌ No theme export to colorscheme file

#### Emacs
- ❌ UI is ASCII placeholder only
- ❌ No face application
- ❌ No theme export to deftheme

---

## Target Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                         Lean4 Proofs                                │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌──────────────┐  │
│  │ ColorSpace  │ │ Conversions │ │   Contrast  │ │ GamutMapping │  │
│  │   Axioms    │ │  Bijection  │ │   Bounds    │ │   Proofs     │  │
│  └─────────────┘ └─────────────┘ └─────────────┘ └──────────────┘  │
└─────────────────────────────────────────────────────────────────────┘
                                │
                                │ Extracted/Verified
                                ▼
┌─────────────────────────────────────────────────────────────────────┐
│                      Haskell Core Library                           │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌──────────────┐  │
│  │  sRGB/XYZ   │ │   OKLAB/    │ │   Base16    │ │   Monitor    │  │
│  │ Conversions │ │   OKLCH     │ │  Generator  │ │ Calibration  │  │
│  └─────────────┘ └─────────────┘ └─────────────┘ └──────────────┘  │
│                                                                     │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐                   │
│  │   WCAG      │ │ ColorBlind  │ │    JSON     │                   │
│  │  Contrast   │ │ Simulation  │ │     FFI     │                   │
│  └─────────────┘ └─────────────┘ └─────────────┘                   │
└─────────────────────────────────────────────────────────────────────┘
                                │
                ┌───────────────┼───────────────┐
                │               │               │
                ▼               ▼               ▼
        ┌───────────┐   ┌───────────┐   ┌───────────┐
        │  VSCode   │   │  Neovim   │   │   Emacs   │
        │ Extension │   │  Plugin   │   │  Package  │
        └───────────┘   └───────────┘   └───────────┘
```

---

## Color Science Foundation

### Color Spaces

1. **sRGB** - Device color space (what monitors display)
   - Gamma-corrected (transfer function)
   - Bounded [0,1]³

2. **Linear RGB** - Physical light intensity
   - No gamma
   - Required for color math

3. **CIE XYZ** - Device-independent, human vision based
   - D65 white point
   - Bridge between RGB and perceptual spaces

4. **OKLAB** - Perceptually uniform Lab space
   - L: Lightness [0,1]
   - a: Green-Red axis
   - b: Blue-Yellow axis
   - Euclidean distance ≈ perceptual difference

5. **OKLCH** - Cylindrical form of OKLAB
   - L: Lightness [0,1]
   - C: Chroma (saturation) [0, ~0.4]
   - H: Hue [0,360)
   - **This is what we use for palette generation**

### Why OKLCH?

```
HSL "50% lightness" across hues:
  Red:    ████████████████  (looks dim)
  Yellow: ████████████████████████████  (looks bright!)
  Blue:   ██████████████  (looks very dim)

OKLCH "50% lightness" across hues:
  Red:    ████████████████████
  Yellow: ████████████████████
  Blue:   ████████████████████  (perceptually equal!)
```

### Conversion Chain

```
sRGB → Linear RGB → XYZ (D65) → OKLAB → OKLCH
                                  ↑
                            All palette math
                            happens here
```

---

## Base16 Palette Generation

Base16 defines 16 colors with semantic meaning:

| Slot | Purpose | Generation Strategy |
|------|---------|---------------------|
| base00 | Background | Black balance adjusted for monitor |
| base01 | Lighter background | base00 + ΔL (perceptual step) |
| base02 | Selection | base00 + 2ΔL |
| base03 | Comments | Low contrast foreground |
| base04 | Dark foreground | Mid contrast |
| base05 | Default foreground | Primary text |
| base06 | Light foreground | Bright text |
| base07 | Brightest | Maximum contrast |
| base08 | Error/Red | Hue-shifted from hero |
| base09 | Warning/Orange | Hue-shifted from hero |
| base0A | **HERO** | User-selected accent |
| base0B | Success/Green | Complementary to hero |
| base0C | Info/Cyan | Triadic to hero |
| base0D | Link/Blue | Split-complementary |
| base0E | Special/Purple | Analogous to hero |
| base0F | Deprecated | Desaturated hero |

### Black Balance

The "black balance" parameter controls base00-base03:

**OLED Monitors** (default 11%):
- True black (L=0) causes "black smear" on OLED
- Slight luminance (L=0.11) prevents this
- But too bright loses contrast

**LCD Monitors** (default 16%):
- LCDs can't display true black anyway
- Backlight bleed means L<5% looks the same
- Higher black point for better gradation

### Perceptual Contrast

WCAG luminance contrast ratio:

```
CR = (L1 + 0.05) / (L2 + 0.05)
```

Where L is relative luminance from sRGB:
```
L = 0.2126 * R + 0.7152 * G + 0.0722 * B
```

Requirements:
- Normal text: CR ≥ 4.5:1 (AA), ≥ 7:1 (AAA)
- Large text: CR ≥ 3:1 (AA), ≥ 4.5:1 (AAA)

---

## Lean4 Proof Obligations

### 1. Conversion Bijectivity

```lean
theorem srgb_linear_roundtrip :
  ∀ c : sRGB, linear_to_srgb (srgb_to_linear c) = c

theorem oklab_oklch_roundtrip :
  ∀ c : OKLAB, oklch_to_oklab (oklab_to_oklch c) = c
```

### 2. Gamut Containment

```lean
theorem gamut_mapped_in_srgb :
  ∀ c : OKLCH, is_in_srgb_gamut (gamut_map c)
```

### 3. Contrast Bounds

```lean
theorem contrast_ratio_positive :
  ∀ c1 c2 : sRGB, contrast_ratio c1 c2 > 0

theorem contrast_ratio_symmetric :
  ∀ c1 c2 : sRGB, contrast_ratio c1 c2 = contrast_ratio c2 c1
```

### 4. Black Balance Validity

```lean
theorem black_balance_bounded :
  ∀ bb : BlackBalance,
    0 ≤ bb.value ∧ bb.value ≤ 0.20 →
    valid_background_luminance (apply_black_balance bb)
```

---

## Implementation Plan

### Phase 1: Core Library (Haskell)

1. Color space types with smart constructors
2. Conversion functions (all directions)
3. OKLCH palette generation
4. Base16 scheme generator
5. JSON serialization

### Phase 2: Lean4 Proofs

1. Color space axioms
2. Conversion bijectivity proofs
3. Gamut mapping proofs
4. Contrast ratio proofs

### Phase 3: FFI Layer

1. C FFI exports from Haskell
2. Python ctypes wrapper
3. Direct Lua FFI for Neovim
4. Dynamic module for Emacs

### Phase 4: Plugin Completion

1. VSCode: Bundle PureScript/TS, add theme installation
2. Neovim: Real color picker, highlight group application
3. Emacs: Widget-based UI, face application

---

## File Structure

```
prism-color-core/
├── lean4/
│   ├── lakefile.lean
│   ├── PrismColor/
│   │   ├── Basic.lean          -- Core types
│   │   ├── SRGB.lean           -- sRGB space
│   │   ├── OKLAB.lean          -- OKLAB/OKLCH
│   │   ├── Conversions.lean    -- All conversions
│   │   ├── Contrast.lean       -- WCAG contrast
│   │   └── Proofs.lean         -- All theorems
│   └── PrismColor.lean         -- Main export
│
├── haskell/
│   ├── prism-color-core.cabal
│   ├── src/
│   │   ├── PrismColor/
│   │   │   ├── Types.hs        -- Core types
│   │   │   ├── SRGB.hs         -- sRGB conversions
│   │   │   ├── OKLAB.hs        -- OKLAB/OKLCH
│   │   │   ├── Palette.hs      -- Base16 generation
│   │   │   ├── Contrast.hs     -- WCAG calculations
│   │   │   └── FFI.hs          -- JSON interface
│   │   └── PrismColor.hs       -- Main export
│   └── test/
│
├── purescript/
│   ├── spago.dhall
│   └── src/
│       └── PrismColor/...      -- Same structure
│
└── docs/
    ├── ARCHITECTURE.md         -- This file
    └── COLOR_SCIENCE.md        -- Deep dive
```

---

## Success Criteria

1. **Zero `sorry`** in Lean4 proofs
2. **100% test coverage** for color conversions
3. **All WCAG contrast requirements** provably satisfied
4. **Roundtrip accuracy** < 1e-10 for all conversions
5. **Real color pickers** in all three editors
6. **One-click theme installation** in all three editors
7. **Live preview** showing actual syntax highlighting
