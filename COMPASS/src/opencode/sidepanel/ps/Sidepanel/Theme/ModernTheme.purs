{-|
Module      : Sidepanel.Theme.ModernTheme
Description : Modern futuristic theme system matching the image styling

Global theme system with CSS variables for colors, typography, spacing, glows, and shadows.
All values are globally editable via CSS custom properties.
-}
module Sidepanel.Theme.ModernTheme where

import Prelude

import Effect (Effect)
import Sidepanel.FFI.DOM as DOM

-- | Theme configuration matching the image styling
type ThemeConfig =
  { colors :: ColorPalette
  , typography :: TypographyConfig
  , spacing :: SpacingConfig
  , effects :: EffectsConfig
  , layout :: LayoutConfig
  }

-- | Color palette
type ColorPalette =
  { background :: String  -- Main dark background
  , backgroundCard :: String  -- Card background (slightly lighter)
  , textPrimary :: String  -- Main headings (white/light grey)
  , textSecondary :: String  -- Subtitles/descriptions
  , accentBlue :: String  -- Primary blue gradient
  , accentPurple :: String  -- Purple gradient
  , accentPink :: String  -- Pink/magenta gradient
  , accentGreen :: String  -- Neon green
  , accentOrange :: String  -- Orange/red gradient
  , glowBlue :: String  -- Blue glow color
  , glowPurple :: String  -- Purple glow color
  , glowPink :: String  -- Pink glow color
  , glowGreen :: String  -- Green glow color
  , glowOrange :: String  -- Orange glow color
  }

-- | Typography configuration
type TypographyConfig =
  { fontFamily :: String
  , fontSizeTitle :: String  -- Main title (36-48px)
  , fontSizeSubtitle :: String  -- Global subtitle (16-18px)
  , fontSizeCardTitle :: String  -- Card titles (20-24px)
  , fontSizeCardDescription :: String  -- Card descriptions (14-16px)
  , fontSizePercentage :: String  -- Percentages (20-24px)
  , fontSizeTag :: String  -- Small tags (12-14px)
  , fontWeightTitle :: String
  , fontWeightCardTitle :: String
  , fontWeightRegular :: String
  }

-- | Spacing configuration
type SpacingConfig =
  { paddingCard :: String  -- Internal card padding
  , gapGrid :: String  -- Gap between grid items
  , gapVertical :: String  -- Vertical spacing between sections
  , gapHorizontal :: String  -- Horizontal gutters
  , borderRadius :: String  -- Rounded corners (8-12px)
  }

-- | Effects configuration (glows, shadows)
type EffectsConfig =
  { glowIntensity :: String  -- Glow blur radius
  , glowSpread :: String  -- Glow spread
  , shadowBlur :: String  -- Shadow blur
  , shadowSpread :: String  -- Shadow spread
  , glowOpacity :: String  -- Glow opacity
  }

-- | Layout configuration
type LayoutConfig =
  { gridColumns :: Int  -- Grid columns
  , cardMinWidth :: String  -- Minimum card width
  , cardMaxWidth :: String  -- Maximum card width
  }

-- | Default theme configuration matching the image
defaultThemeConfig :: ThemeConfig
defaultThemeConfig =
  { colors:
      { background: "#1A1A1A"
      , backgroundCard: "#2C2C2C"
      , textPrimary: "#FFFFFF"
      , textSecondary: "#E0E0E0"
      , accentBlue: "#54AEFF"
      , accentPurple: "#9D4EDD"
      , accentPink: "#FF006E"
      , accentGreen: "#00FF88"
      , accentOrange: "#FF6B35"
      , glowBlue: "#54AEFF"
      , glowPurple: "#9D4EDD"
      , glowPink: "#FF006E"
      , glowGreen: "#00FF88"
      , glowOrange: "#FF6B35"
      }
  , typography:
      { fontFamily: "'Inter', 'Montserrat', 'Roboto', -apple-system, BlinkMacSystemFont, sans-serif"
      , fontSizeTitle: "42px"
      , fontSizeSubtitle: "17px"
      , fontSizeCardTitle: "22px"
      , fontSizeCardDescription: "15px"
      , fontSizePercentage: "22px"
      , fontSizeTag: "13px"
      , fontWeightTitle: "600"
      , fontWeightCardTitle: "600"
      , fontWeightRegular: "400"
      }
  , spacing:
      { paddingCard: "24px"
      , gapGrid: "20px"
      , gapVertical: "32px"
      , gapHorizontal: "24px"
      , borderRadius: "10px"
      }
  , effects:
      { glowIntensity: "12px"
      , glowSpread: "2px"
      , shadowBlur: "8px"
      , shadowSpread: "0px"
      , glowOpacity: "0.6"
      }
  , layout:
      { gridColumns: 3
      , cardMinWidth: "300px"
      , cardMaxWidth: "100%"
      }
  }

-- | Generate CSS custom properties from theme config
generateThemeCSS :: ThemeConfig -> String
generateThemeCSS config =
  let colors = config.colors
      typography = config.typography
      spacing = config.spacing
      effects = config.effects
      layout = config.layout
  in
    ":root {\n" <>
    "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
    "     BACKGROUND COLORS\n" <>
    "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
    "  --theme-bg-primary: " <> colors.background <> ";\n" <>
    "  --theme-bg-card: " <> colors.backgroundCard <> ";\n" <>
    "  --theme-bg-overlay: rgba(44, 44, 44, 0.8);\n" <>
    "\n" <>
    "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
    "     TEXT COLORS\n" <>
    "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
    "  --theme-text-primary: " <> colors.textPrimary <> ";\n" <>
    "  --theme-text-secondary: " <> colors.textSecondary <> ";\n" <>
    "  --theme-text-muted: rgba(224, 224, 224, 0.7);\n" <>
    "\n" <>
    "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
    "     ACCENT COLORS (Gradients)\n" <>
    "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
    "  --theme-accent-blue: " <> colors.accentBlue <> ";\n" <>
    "  --theme-accent-purple: " <> colors.accentPurple <> ";\n" <>
    "  --theme-accent-pink: " <> colors.accentPink <> ";\n" <>
    "  --theme-accent-green: " <> colors.accentGreen <> ";\n" <>
    "  --theme-accent-orange: " <> colors.accentOrange <> ";\n" <>
    "\n" <>
    "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
    "     GRADIENT DEFINITIONS\n" <>
    "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
    "  --theme-gradient-blue-purple: linear-gradient(135deg, " <> colors.accentBlue <> " 0%, " <> colors.accentPurple <> " 100%);\n" <>
    "  --theme-gradient-pink-purple: linear-gradient(135deg, " <> colors.accentPink <> " 0%, " <> colors.accentPurple <> " 100%);\n" <>
    "  --theme-gradient-multi: radial-gradient(circle, rgba(255, 255, 255, 0.9) 0%, " <> colors.accentPink <> " 30%, " <> colors.accentPurple <> " 60%, " <> colors.accentBlue <> " 100%);\n" <>
    "\n" <>
    "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
    "     GLOW COLORS\n" <>
    "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
    "  --theme-glow-blue: " <> colors.glowBlue <> ";\n" <>
    "  --theme-glow-purple: " <> colors.glowPurple <> ";\n" <>
    "  --theme-glow-pink: " <> colors.glowPink <> ";\n" <>
    "  --theme-glow-green: " <> colors.glowGreen <> ";\n" <>
    "  --theme-glow-orange: " <> colors.glowOrange <> ";\n" <>
    "\n" <>
    "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
    "     TYPOGRAPHY\n" <>
    "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
    "  --theme-font-family: " <> typography.fontFamily <> ";\n" <>
    "  --theme-font-size-title: " <> typography.fontSizeTitle <> ";\n" <>
    "  --theme-font-size-subtitle: " <> typography.fontSizeSubtitle <> ";\n" <>
    "  --theme-font-size-card-title: " <> typography.fontSizeCardTitle <> ";\n" <>
    "  --theme-font-size-card-description: " <> typography.fontSizeCardDescription <> ";\n" <>
    "  --theme-font-size-percentage: " <> typography.fontSizePercentage <> ";\n" <>
    "  --theme-font-size-tag: " <> typography.fontSizeTag <> ";\n" <>
    "  --theme-font-weight-title: " <> typography.fontWeightTitle <> ";\n" <>
    "  --theme-font-weight-card-title: " <> typography.fontWeightCardTitle <> ";\n" <>
    "  --theme-font-weight-regular: " <> typography.fontWeightRegular <> ";\n" <>
    "\n" <>
    "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
    "     SPACING\n" <>
    "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
    "  --theme-padding-card: " <> spacing.paddingCard <> ";\n" <>
    "  --theme-gap-grid: " <> spacing.gapGrid <> ";\n" <>
    "  --theme-gap-vertical: " <> spacing.gapVertical <> ";\n" <>
    "  --theme-gap-horizontal: " <> spacing.gapHorizontal <> ";\n" <>
    "  --theme-border-radius: " <> spacing.borderRadius <> ";\n" <>
    "\n" <>
    "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
    "     EFFECTS (Glows & Shadows)\n" <>
    "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
    "  --theme-glow-intensity: " <> effects.glowIntensity <> ";\n" <>
    "  --theme-glow-spread: " <> effects.glowSpread <> ";\n" <>
    "  --theme-shadow-blur: " <> effects.shadowBlur <> ";\n" <>
    "  --theme-shadow-spread: " <> effects.shadowSpread <> ";\n" <>
    "  --theme-glow-opacity: " <> effects.glowOpacity <> ";\n" <>
    "\n" <>
    "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
    "     GLOW EFFECTS (Box Shadows)\n" <>
    "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
    "  --theme-glow-blue: 0 0 " <> effects.glowIntensity <> " " <> effects.glowSpread <> " rgba(84, 174, 255, " <> effects.glowOpacity <> ");\n" <>
    "  --theme-glow-purple: 0 0 " <> effects.glowIntensity <> " " <> effects.glowSpread <> " rgba(157, 78, 221, " <> effects.glowOpacity <> ");\n" <>
    "  --theme-glow-pink: 0 0 " <> effects.glowIntensity <> " " <> effects.glowSpread <> " rgba(255, 0, 110, " <> effects.glowOpacity <> ");\n" <>
    "  --theme-glow-green: 0 0 " <> effects.glowIntensity <> " " <> effects.glowSpread <> " rgba(0, 255, 136, " <> effects.glowOpacity <> ");\n" <>
    "  --theme-glow-orange: 0 0 " <> effects.glowIntensity <> " " <> effects.glowSpread <> " rgba(255, 107, 53, " <> effects.glowOpacity <> ");\n" <>
    "\n" <>
    "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
    "     LAYOUT\n" <>
    "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
    "  --theme-grid-columns: " <> show layout.gridColumns <> ";\n" <>
    "  --theme-card-min-width: " <> layout.cardMinWidth <> ";\n" <>
    "  --theme-card-max-width: " <> layout.cardMaxWidth <> ";\n" <>
    "}\n"

-- | CSS rules for theme classes (from ModernTheme.css)
themeCSSRules :: String
themeCSSRules =
  "/* Modern Futuristic Theme - Matching Image Styling */\n" <>
  "/* Base styles applied globally */\n" <>
  "* { box-sizing: border-box; }\n" <>
  "html, body { margin: 0; padding: 0; }\n" <>
  "\n" <>
  "/* Card styles (Bento Box Layout) */\n" <>
  ".theme-card {\n" <>
  "  background: var(--theme-bg-card, #2C2C2C);\n" <>
  "  border-radius: var(--theme-border-radius, 10px);\n" <>
  "  padding: var(--theme-padding-card, 24px);\n" <>
  "  box-shadow: 0 4px var(--theme-shadow-blur, 8px) rgba(0, 0, 0, 0.3), inset 0 0 20px rgba(255, 255, 255, 0.02);\n" <>
  "  backdrop-filter: blur(10px);\n" <>
  "  border: 1px solid rgba(255, 255, 255, 0.05);\n" <>
  "  transition: transform 0.2s ease, box-shadow 0.2s ease;\n" <>
  "}\n" <>
  ".theme-card:hover {\n" <>
  "  transform: translateY(-2px);\n" <>
  "  box-shadow: 0 8px var(--theme-shadow-blur, 8px) rgba(0, 0, 0, 0.4), var(--theme-glow-blue, 0 0 12px 2px rgba(84, 174, 255, 0.6));\n" <>
  "}\n" <>
  "\n" <>
  "/* Typography */\n" <>
  ".theme-title {\n" <>
  "  font-size: var(--theme-font-size-title, 42px);\n" <>
  "  font-weight: var(--theme-font-weight-title, 600);\n" <>
  "  color: var(--theme-text-primary, #FFFFFF);\n" <>
  "  line-height: 1.2;\n" <>
  "  margin: 0;\n" <>
  "}\n" <>
  ".theme-subtitle {\n" <>
  "  font-size: var(--theme-font-size-subtitle, 17px);\n" <>
  "  font-weight: var(--theme-font-weight-regular, 400);\n" <>
  "  color: var(--theme-text-secondary, #E0E0E0);\n" <>
  "  line-height: 1.5;\n" <>
  "  margin: 0;\n" <>
  "}\n" <>
  ".theme-card-title {\n" <>
  "  font-size: var(--theme-font-size-card-title, 22px);\n" <>
  "  font-weight: var(--theme-font-weight-card-title, 600);\n" <>
  "  color: var(--theme-text-primary, #FFFFFF);\n" <>
  "  line-height: 1.3;\n" <>
  "  margin: 0 0 8px 0;\n" <>
  "}\n" <>
  ".theme-card-description {\n" <>
  "  font-size: var(--theme-font-size-card-description, 15px);\n" <>
  "  font-weight: var(--theme-font-weight-regular, 400);\n" <>
  "  color: var(--theme-text-secondary, #E0E0E0);\n" <>
  "  line-height: 1.5;\n" <>
  "  margin: 0;\n" <>
  "}\n" <>
  "\n" <>
  "/* Grid layout (Bento Box) */\n" <>
  ".theme-grid {\n" <>
  "  display: grid;\n" <>
  "  grid-template-columns: repeat(var(--theme-grid-columns, 3), 1fr);\n" <>
  "  gap: var(--theme-gap-grid, 20px);\n" <>
  "  padding: var(--theme-gap-horizontal, 24px);\n" <>
  "}\n" <>
  "\n" <>
  "/* Buttons */\n" <>
  ".theme-button {\n" <>
  "  background: var(--theme-bg-card, #2C2C2C);\n" <>
  "  color: var(--theme-text-primary, #FFFFFF);\n" <>
  "  border: 1px solid rgba(255, 255, 255, 0.1);\n" <>
  "  border-radius: var(--theme-border-radius, 10px);\n" <>
  "  padding: 12px 24px;\n" <>
  "  font-size: var(--theme-font-size-card-description, 15px);\n" <>
  "  font-weight: var(--theme-font-weight-regular, 400);\n" <>
  "  cursor: pointer;\n" <>
  "  transition: all 0.2s ease;\n" <>
  "  box-shadow: 0 2px 4px rgba(0, 0, 0, 0.2);\n" <>
  "}\n" <>
  ".theme-button:hover {\n" <>
  "  background: rgba(255, 255, 255, 0.05);\n" <>
  "  box-shadow: var(--theme-glow-blue, 0 0 12px 2px rgba(84, 174, 255, 0.6));\n" <>
  "  transform: translateY(-1px);\n" <>
  "}\n" <>
  "\n" <>
  "/* Glow effects */\n" <>
  ".theme-glow-blue { box-shadow: var(--theme-glow-blue, 0 0 12px 2px rgba(84, 174, 255, 0.6)); }\n" <>
  ".theme-glow-purple { box-shadow: var(--theme-glow-purple, 0 0 12px 2px rgba(157, 78, 221, 0.6)); }\n" <>
  ".theme-glow-pink { box-shadow: var(--theme-glow-pink, 0 0 12px 2px rgba(255, 0, 110, 0.6)); }\n" <>
  ".theme-glow-green { box-shadow: var(--theme-glow-green, 0 0 12px 2px rgba(0, 255, 136, 0.6)); }\n" <>
  ".theme-glow-orange { box-shadow: var(--theme-glow-orange, 0 0 12px 2px rgba(255, 107, 53, 0.6)); }\n"

-- | Apply theme to document
applyTheme :: ThemeConfig -> Effect Unit
applyTheme config = do
  let css = generateThemeCSS config <> "\n\n" <> themeCSSRules
  DOM.injectCSSWithId "modern-theme-styles" css

-- | Update theme color
updateThemeColor :: String -> String -> Effect Unit
updateThemeColor colorVar value = do
  DOM.setCSSVariable colorVar value

-- | Update theme spacing
updateThemeSpacing :: String -> String -> Effect Unit
updateThemeSpacing spacingVar value = do
  DOM.setCSSVariable spacingVar value

-- | Update theme typography
updateThemeTypography :: String -> String -> Effect Unit
updateThemeTypography typographyVar value = do
  DOM.setCSSVariable typographyVar value

-- | Update theme effects
updateThemeEffects :: String -> String -> Effect Unit
updateThemeEffects effectsVar value = do
  DOM.setCSSVariable effectsVar value
