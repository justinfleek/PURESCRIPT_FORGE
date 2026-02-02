-- | CSS token system using PRISM colors and Fleek tokens
-- | Based on spec 47-THEMING.md, 94-FLEEK-CSS-TOKENS.md
module Sidepanel.Theme.CSS where

import Prelude
import Effect (Effect)
import Sidepanel.Theme.Prism (Base16Colors, FleekColors, fleekColors)
import Sidepanel.FFI.DOM as DOM

-- | Generate CSS custom properties from PRISM theme
generateCSS :: Base16Colors -> FleekColors -> String
generateCSS base16 fleek =
  ":root {\n" <>
  "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
  "     FLEEK BRAND COLORS\n" <>
  "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
  "  --fleek-blue: " <> fleek.fleekBlue <> ";\n" <>
  "  --fleek-green: " <> fleek.fleekGreen <> ";\n" <>
  "  --fleek-yellow: " <> fleek.fleekYellow <> ";\n" <>
  "  --fleek-orange: " <> fleek.fleekOrange <> ";\n" <>
  "\n" <>
  "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
  "     BACKGROUND COLORS (from PRISM Base16)\n" <>
  "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
  "  --bg-base: " <> base16.base00 <> ";\n" <>
  "  --bg-surface: " <> base16.base01 <> ";\n" <>
  "  --bg-elevated: " <> base16.base02 <> ";\n" <>
  "  --bg-overlay: " <> base16.base03 <> ";\n" <>
  "\n" <>
  "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
  "     TEXT COLORS (from PRISM Base16)\n" <>
  "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
  "  --text-primary: " <> base16.base05 <> ";\n" <>
  "  --text-secondary: " <> base16.base04 <> ";\n" <>
  "  --text-tertiary: " <> base16.base03 <> ";\n" <>
  "  --text-disabled: " <> base16.base02 <> ";\n" <>
  "\n" <>
  "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
  "     SEMANTIC COLORS (from PRISM Base16)\n" <>
  "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
  "  --color-success: " <> base16.base0B <> ";\n" <>
  "  --color-warning: " <> base16.base09 <> ";\n" <>
  "  --color-error: " <> base16.base08 <> ";\n" <>
  "  --color-info: " <> base16.base0C <> ";\n" <>
  "  --color-primary: " <> base16.base0D <> ";\n" <>
  "  --color-hero: " <> base16.base0A <> ";\n" <>
  "\n" <>
  "  /* ═══════════════════════════════════════════════════════════════════════\n" <>
  "     DIEM COLORS (Fleek brand)\n" <>
  "     ═══════════════════════════════════════════════════════════════════════ */\n" <>
  "  --diem-healthy: " <> fleek.fleekGreen <> ";\n" <>
  "  --diem-caution: " <> fleek.fleekYellow <> ";\n" <>
  "  --diem-warning: " <> fleek.fleekOrange <> ";\n" <>
  "  --diem-critical: " <> base16.base08 <> ";\n" <>
  "}\n"

-- | Apply theme to document
applyTheme :: String -> Effect Unit
applyTheme css = do
  DOM.ensureThemeStyleElement
  DOM.injectCSS css
