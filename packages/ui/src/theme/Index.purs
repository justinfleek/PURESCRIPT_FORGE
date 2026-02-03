-- | UI Theme Module Index
-- |
-- | Re-exports all theme modules for convenient importing.
-- |
-- | PRISM Color System Integration:
-- | - Types: Bounded color types (UnitInterval, Hue), OKLCH, Base16, MonitorType
-- | - Color: Full conversion chain (sRGB <-> Linear <-> XYZ <-> OKLAB <-> OKLCH)
-- | - Contrast: WCAG 2.1 compliance verification
-- | - Palette: Monochromatic Base16 generation
-- | - Resolve: Theme token generation
-- | - Loader: DOM CSS injection
-- | - Context: React-style theme context
module Forge.UI.Theme
  ( module Forge.UI.Theme.Types
  , module Forge.UI.Theme.Color
  , module Forge.UI.Theme.Contrast
  , module Forge.UI.Theme.Palette
  , module Forge.UI.Theme.Resolve
  , module Forge.UI.Theme.Loader
  , module Forge.UI.Theme.Context
  ) where

-- Types: Core type definitions with PRISM bounded values
import Forge.UI.Theme.Types 
  ( UnitInterval, mkUnitInterval, clampUnit, unUnit
  , Hue, mkHue, normalizeHue, unHue
  , HexColor, RGB, SRGB, LinearRGB, XYZ, OKLAB, OKLCH, mkOKLCH
  , MonitorType(..), BlackBalance, mkBlackBalance, defaultBlackBalance, unBlackBalance
  , ThemeMode(..)
  , Base16Palette, Base16Slot(..)
  , ThemeConfig, ThemeSeedColors, ThemeVariant, DesktopTheme
  , TokenCategory(..), ThemeToken, CssVarRef, ColorValue, ResolvedTheme
  )

-- Color: Complete PRISM conversion chain
import Forge.UI.Theme.Color 
  ( hexToRgb, rgbToHex, hexToSrgb, srgbToHex
  , srgbToLinear, linearToSrgb, srgbToLinearComponent, linearToSrgbComponent
  , linearToXYZ, xyzToLinear
  , xyzToOklab, oklabToXYZ
  , oklabToOklch, oklchToOklab
  , srgbToOklch, oklchToSrgb, hexToOklch, oklchToHex
  , relativeLuminance, relativeLuminanceHex
  , oklchWithLightness, oklchWithChroma, oklchWithHue, oklchRotateHue
  , generateScale, generateNeutralScale, generateAlphaScale
  , mixColors, lighten, darken, withAlpha
  )

-- Contrast: WCAG compliance
import Forge.UI.Theme.Contrast
  ( contrastRatio, contrastRatioHex, contrastRatioSrgb
  , WCAGLevel(..), TextSize(..)
  , wcagCompliance, meetsWCAG, meetsWCAGHex, minContrastFor
  , adjustLightnessForContrast, findAccessibleLightness
  )

-- Palette: Monochromatic Base16 generation
import Forge.UI.Theme.Palette
  ( generatePalette, generatePaletteFromConfig
  , generateBackgroundRamp, generateForegroundRamp, generateAccentColors
  , darkVariantLightnesses, lightVariantLightnesses
  , monochromaticColor
  )

-- Resolve: Token generation from seeds
import Forge.UI.Theme.Resolve
  ( resolveThemeVariant, resolveTheme, themeToCss
  , generateNeutralAlphaScale
  )

-- Loader: DOM application
import Forge.UI.Theme.Loader
  ( applyTheme, loadThemeFromUrl, getActiveTheme, removeTheme, setColorScheme
  )

-- Context: Theme management
import Forge.UI.Theme.Context 
  ( ThemeContext, ThemeProvider, useTheme, ColorScheme(..)
  )
