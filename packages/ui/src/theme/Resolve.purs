-- | Theme Resolution - Generate Theme Tokens from Seeds
-- |
-- | Resolves a theme variant (light/dark) into a complete set of
-- | CSS custom property tokens. Generates color scales from seed
-- | colors and applies semantic mappings.
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/theme/resolve.ts
module Forge.UI.Theme.Resolve
  ( resolveThemeVariant
  , resolveTheme
  , themeToCss
  , generateNeutralAlphaScale
  , ensureSeedVariety
  ) where

import Prelude

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Tuple (Tuple(..))
import Forge.UI.Theme.Color (generateNeutralScale, generateScale, hexToOklch, oklchToHex, withAlpha)
import Forge.UI.Theme.Types (ColorValue, DesktopTheme, HexColor, ResolvedTheme, ThemeSeedColors, ThemeVariant, mkOKLCH, unHue, unUnit)
import Math (abs)

-- | Ensure seed colors have sufficient hue variety for visual distinction.
-- | If seeds are too similar (monochromatic), rotate hues to create variety.
-- | This fixes the issue where headings, list items, and body text look identical.
ensureSeedVariety :: ThemeSeedColors -> ThemeSeedColors
ensureSeedVariety seeds =
  let
    -- Get the primary hue as the "hero" hue
    primaryOklch = hexToOklch seeds.primary
    heroHue = unHue primaryOklch.h
    heroChroma = primaryOklch.c
    heroLightness = unUnit primaryOklch.l
    
    -- Check if a color is within 30 degrees of primary (too similar)
    isSimilar :: HexColor -> Boolean
    isSimilar hex = 
      let oklch = hexToOklch hex
          hueDiff = abs (unHue oklch.h - heroHue)
          normalizedDiff = if hueDiff > 180.0 then 360.0 - hueDiff else hueDiff
      in normalizedDiff < 30.0
    
    -- Create a rotated color if the original is too similar to primary
    rotateIfSimilar :: HexColor -> Number -> HexColor
    rotateIfSimilar hex targetOffset =
      if isSimilar hex
        then oklchToHex (mkOKLCH heroLightness heroChroma (heroHue + targetOffset))
        else hex
  in
    seeds
      { success = rotateIfSimilar seeds.success 120.0    -- Triadic (green region)
      , warning = rotateIfSimilar seeds.warning 45.0     -- Analogous warm (orange)
      , error = rotateIfSimilar seeds.error (-30.0)      -- Analogous cool (red/pink)
      , info = rotateIfSimilar seeds.info 180.0          -- Complementary (cyan/blue)
      , interactive = seeds.interactive                   -- Keep interactive as hero
      , diffAdd = rotateIfSimilar seeds.diffAdd 120.0    -- Same as success
      , diffDelete = rotateIfSimilar seeds.diffDelete (-30.0) -- Same as error
      }

-- | Resolve a theme variant (light or dark) to a complete token map
resolveThemeVariant :: ThemeVariant -> Boolean -> ResolvedTheme
resolveThemeVariant variant isDark =
  let
    -- Ensure seeds have variety for visual distinction
    seeds = ensureSeedVariety variant.seeds
    overrides = variant.overrides
    
    -- Generate color scales from (potentially adjusted) seeds
    neutral = generateNeutralScale seeds.neutral isDark
    primary = generateScale seeds.primary isDark
    success = generateScale seeds.success isDark
    warning = generateScale seeds.warning isDark
    error = generateScale seeds.error isDark
    info = generateScale seeds.info isDark
    interactive = generateScale seeds.interactive isDark
    diffAdd = generateScale seeds.diffAdd isDark
    diffDelete = generateScale seeds.diffDelete isDark
    
    neutralAlpha = generateNeutralAlphaScale neutral isDark
    
    -- Helper to get array element safely
    get :: Array String -> Int -> String
    get arr idx = fromMaybe "#000000" (Array.index arr idx)
    
    n = get neutral
    na = get neutralAlpha
    p = get primary
    s = get success
    w = get warning
    e = get error
    i = get info
    int = get interactive
    da = get diffAdd
    dd = get diffDelete
    
    -- Build token map
    tokens = Map.fromFoldable
      -- Background
      [ Tuple "background-base" (n 0)
      , Tuple "background-weak" (n 2)
      , Tuple "background-strong" (n 0)
      , Tuple "background-stronger" (if isDark then n 1 else "#fcfcfc")
      
      -- Surface
      , Tuple "surface-base" (na 1)
      , Tuple "base" (na 1)
      , Tuple "surface-base-hover" (na 2)
      , Tuple "surface-base-active" (na 2)
      , Tuple "surface-base-interactive-active" (withAlpha (int 2) 0.3)
      , Tuple "base2" (na 1)
      , Tuple "base3" (na 1)
      , Tuple "surface-inset-base" (na 1)
      , Tuple "surface-inset-base-hover" (na 2)
      , Tuple "surface-inset-strong" (if isDark then withAlpha (n 0) 0.5 else withAlpha (n 3) 0.09)
      , Tuple "surface-raised-base" (na 0)
      , Tuple "surface-float-base" (if isDark then n 0 else n 11)
      , Tuple "surface-float-base-hover" (if isDark then n 1 else n 10)
      , Tuple "surface-raised-base-hover" (na 1)
      , Tuple "surface-raised-base-active" (na 2)
      , Tuple "surface-raised-strong" (if isDark then na 3 else n 0)
      , Tuple "surface-raised-strong-hover" (if isDark then na 5 else "#ffffff")
      , Tuple "surface-raised-stronger" (if isDark then na 5 else "#ffffff")
      , Tuple "surface-raised-stronger-hover" (if isDark then na 6 else "#ffffff")
      , Tuple "surface-weak" (na 2)
      , Tuple "surface-weaker" (na 3)
      , Tuple "surface-strong" (if isDark then na 6 else "#ffffff")
      , Tuple "surface-raised-stronger-non-alpha" (if isDark then n 2 else "#ffffff")
      
      -- Brand surface
      , Tuple "surface-brand-base" (p 8)
      , Tuple "surface-brand-hover" (p 9)
      
      -- Interactive surface
      , Tuple "surface-interactive-base" (int 2)
      , Tuple "surface-interactive-hover" (int 3)
      , Tuple "surface-interactive-weak" (int 1)
      , Tuple "surface-interactive-weak-hover" (int 2)
      
      -- Status surfaces
      , Tuple "surface-success-base" (s 2)
      , Tuple "surface-success-weak" (s 1)
      , Tuple "surface-success-strong" (s 8)
      , Tuple "surface-warning-base" (w 2)
      , Tuple "surface-warning-weak" (w 1)
      , Tuple "surface-warning-strong" (w 8)
      , Tuple "surface-critical-base" (e 2)
      , Tuple "surface-critical-weak" (e 1)
      , Tuple "surface-critical-strong" (e 8)
      , Tuple "surface-info-base" (i 2)
      , Tuple "surface-info-weak" (i 1)
      , Tuple "surface-info-strong" (i 8)
      
      -- Diff surfaces
      , Tuple "surface-diff-unchanged-base" (if isDark then n 0 else "#ffffff00")
      , Tuple "surface-diff-skip-base" (if isDark then na 0 else n 1)
      , Tuple "surface-diff-hidden-base" (int (if isDark then 1 else 2))
      , Tuple "surface-diff-hidden-weak" (int (if isDark then 0 else 1))
      , Tuple "surface-diff-hidden-weaker" (int (if isDark then 2 else 0))
      , Tuple "surface-diff-hidden-strong" (int 4)
      , Tuple "surface-diff-hidden-stronger" (int (if isDark then 10 else 8))
      , Tuple "surface-diff-add-base" (da 2)
      , Tuple "surface-diff-add-weak" (da (if isDark then 3 else 1))
      , Tuple "surface-diff-add-weaker" (da (if isDark then 2 else 0))
      , Tuple "surface-diff-add-strong" (da 4)
      , Tuple "surface-diff-add-stronger" (da (if isDark then 10 else 8))
      , Tuple "surface-diff-delete-base" (dd 2)
      , Tuple "surface-diff-delete-weak" (dd (if isDark then 3 else 1))
      , Tuple "surface-diff-delete-weaker" (dd (if isDark then 2 else 0))
      , Tuple "surface-diff-delete-strong" (dd (if isDark then 4 else 5))
      , Tuple "surface-diff-delete-stronger" (dd (if isDark then 10 else 8))
      
      -- Input
      , Tuple "input-base" (if isDark then n 1 else n 0)
      , Tuple "input-hover" (n 1)
      , Tuple "input-active" (int 0)
      , Tuple "input-selected" (int 3)
      , Tuple "input-focus" (int 0)
      , Tuple "input-disabled" (n 3)
      
      -- Text
      , Tuple "text-base" (n 10)
      , Tuple "text-weak" (n 8)
      , Tuple "text-weaker" (n 7)
      , Tuple "text-strong" (n 11)
      , Tuple "text-invert-base" (if isDark then n 10 else n 1)
      , Tuple "text-invert-weak" (if isDark then n 8 else n 2)
      , Tuple "text-invert-weaker" (if isDark then n 7 else n 3)
      , Tuple "text-invert-strong" (if isDark then n 11 else n 0)
      , Tuple "text-interactive-base" (int (if isDark then 10 else 8))
      , Tuple "text-on-brand-base" (na 10)
      , Tuple "text-on-interactive-base" (if isDark then n 11 else n 0)
      , Tuple "text-on-interactive-weak" (na 10)
      , Tuple "text-on-success-base" (s (if isDark then 8 else 9))
      , Tuple "text-on-critical-base" (e (if isDark then 8 else 9))
      , Tuple "text-on-critical-weak" (e 7)
      , Tuple "text-on-critical-strong" (e 11)
      , Tuple "text-on-warning-base" (na 10)
      , Tuple "text-on-info-base" (na 10)
      , Tuple "text-diff-add-base" (da 10)
      , Tuple "text-diff-delete-base" (dd (if isDark then 8 else 9))
      , Tuple "text-diff-delete-strong" (dd 11)
      , Tuple "text-diff-add-strong" (da (if isDark then 7 else 11))
      
      -- Button
      , Tuple "button-secondary-base" (if isDark then n 2 else n 0)
      , Tuple "button-secondary-hover" (if isDark then n 3 else n 1)
      , Tuple "button-ghost-hover" (na 1)
      , Tuple "button-ghost-hover2" (na 2)
      
      -- Border
      , Tuple "border-base" (na 6)
      , Tuple "border-hover" (na 7)
      , Tuple "border-active" (na 8)
      , Tuple "border-selected" (withAlpha (int 8) (if isDark then 0.9 else 0.99))
      , Tuple "border-disabled" (na 7)
      , Tuple "border-focus" (na 8)
      , Tuple "border-weak-base" (na (if isDark then 5 else 4))
      , Tuple "border-strong-base" (na (if isDark then 7 else 6))
      , Tuple "border-color" "#ffffff"
      
      -- Icon
      , Tuple "icon-base" (n 8)
      , Tuple "icon-hover" (n (if isDark then 9 else 10))
      , Tuple "icon-active" (n (if isDark then 10 else 11))
      , Tuple "icon-selected" (n 11)
      , Tuple "icon-disabled" (n (if isDark then 6 else 7))
      , Tuple "icon-focus" (n 11)
      , Tuple "icon-invert-base" (if isDark then n 0 else "#ffffff")
      , Tuple "icon-brand-base" (if isDark then "#ffffff" else n 11)
      , Tuple "icon-interactive-base" (int 8)
      , Tuple "icon-success-base" (s 6)
      , Tuple "icon-warning-base" (w 6)
      , Tuple "icon-critical-base" (e (if isDark then 8 else 9))
      , Tuple "icon-info-base" (i 6)
      , Tuple "icon-diff-add-base" (da 10)
      , Tuple "icon-diff-delete-base" (dd (if isDark then 8 else 9))
      
      -- Syntax highlighting - USE THEME SCALES for consistent variety
      -- Comment: muted neutral
      , Tuple "syntax-comment" (n 6)
      -- Regexp: info color
      , Tuple "syntax-regexp" (i 8)
      -- String: success color (green family)
      , Tuple "syntax-string" (s 9)
      -- Keyword: primary accent (THE hero color)
      , Tuple "syntax-keyword" (p 9)
      -- Primitive: warning color (warm, numbers/booleans)
      , Tuple "syntax-primitive" (w 9)
      -- Operator: muted
      , Tuple "syntax-operator" (n 7)
      -- Variable: bright neutral
      , Tuple "syntax-variable" (n 10)
      -- Property: interactive color (distinct from keyword)
      , Tuple "syntax-property" (int 9)
      -- Type: info color (cool, structural)
      , Tuple "syntax-type" (i 9)
      -- Constant: warning brighter (warm constants)
      , Tuple "syntax-constant" (w 10)
      -- Punctuation: very muted
      , Tuple "syntax-punctuation" (n 5)
      -- Object: neutral strong
      , Tuple "syntax-object" (n 11)
      -- Semantic status colors
      , Tuple "syntax-success" (s 9)
      , Tuple "syntax-warning" (w 9)
      , Tuple "syntax-critical" (e 9)
      , Tuple "syntax-info" (i 9)
      -- Diff colors
      , Tuple "syntax-diff-add" (da 10)
      , Tuple "syntax-diff-delete" (dd 10)
      , Tuple "syntax-diff-unknown" (e 8)
      
      -- Markdown - USE THEME SCALES for variety within the palette
      -- Heading: primary accent (high visibility)
      , Tuple "markdown-heading" (p 9)
      -- Text: neutral foreground
      , Tuple "markdown-text" (n 11)
      -- Link: info color (distinct from heading)
      , Tuple "markdown-link" (i 9)
      -- Link text: info but slightly different
      , Tuple "markdown-link-text" (i 8)
      -- Code: success color (green family - distinct from other elements)
      , Tuple "markdown-code" (s 9)
      -- Blockquote: warning color (warm, distinct from cool link/info)
      , Tuple "markdown-block-quote" (w 8)
      -- Emphasis: warning family (warm accent)
      , Tuple "markdown-emph" (w 9)
      -- Strong: primary but brighter
      , Tuple "markdown-strong" (p 10)
      -- HR: muted neutral
      , Tuple "markdown-horizontal-rule" (n 6)
      -- List item: interactive color (DISTINCT from heading!)
      , Tuple "markdown-list-item" (int 9)
      -- Code block: same as inline code
      , Tuple "markdown-code-block" (s 8)
      
      -- Avatar
      , Tuple "avatar-background-pink" (if isDark then "#501b3f" else "#feeef8")
      , Tuple "avatar-background-mint" (if isDark then "#033a34" else "#e1fbf4")
      , Tuple "avatar-background-orange" (if isDark then "#5f2a06" else "#fff1e7")
      , Tuple "avatar-background-purple" (if isDark then "#432155" else "#f9f1fe")
      , Tuple "avatar-background-cyan" (if isDark then "#0f3058" else "#e7f9fb")
      , Tuple "avatar-background-lime" (if isDark then "#2b3711" else "#eefadc")
      , Tuple "avatar-text-pink" (if isDark then "#e34ba9" else "#cd1d8d")
      , Tuple "avatar-text-mint" (if isDark then "#95f3d9" else "#147d6f")
      , Tuple "avatar-text-orange" (if isDark then "#ff802b" else "#ed5f00")
      , Tuple "avatar-text-purple" (if isDark then "#9d5bd2" else "#8445bc")
      , Tuple "avatar-text-cyan" (if isDark then "#369eff" else "#0894b3")
      , Tuple "avatar-text-lime" (if isDark then "#c4f042" else "#5d770d")
      ]
    
    -- Apply overrides
    finalTokens = Map.union overrides tokens
  in
    finalTokens

-- | Generate neutral alpha scale for semi-transparent overlays
generateNeutralAlphaScale :: Array HexColor -> Boolean -> Array HexColor
generateNeutralAlphaScale neutralScale isDark =
  let
    alphas = if isDark
      then [0.02, 0.04, 0.08, 0.12, 0.16, 0.2, 0.26, 0.36, 0.44, 0.52, 0.72, 0.94]
      else [0.01, 0.03, 0.06, 0.09, 0.12, 0.15, 0.2, 0.27, 0.46, 0.61, 0.5, 0.87]
  in
    Array.zipWith (\hex alpha ->
      let 
        baseOklch = hexToOklch hex
        targetL = if isDark then 0.1 + alpha * 0.8 else 1.0 - alpha * 0.8
        newL = baseOklch.l * alpha + targetL * (1.0 - alpha)
      in oklchToHex { l: newL, c: baseOklch.c, h: baseOklch.h }
    ) neutralScale alphas

-- | Resolve both light and dark variants of a theme
resolveTheme :: DesktopTheme -> { light :: ResolvedTheme, dark :: ResolvedTheme }
resolveTheme theme =
  { light: resolveThemeVariant theme.light false
  , dark: resolveThemeVariant theme.dark true
  }

-- | Convert resolved theme tokens to CSS custom properties
themeToCss :: ResolvedTheme -> String
themeToCss tokens =
  Map.foldlWithKey (\acc key value -> 
    acc <> "--" <> key <> ": " <> value <> ";\n  "
  ) "" tokens
