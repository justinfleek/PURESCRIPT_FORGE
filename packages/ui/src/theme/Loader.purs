-- | Theme Loader - Dynamic Theme Application
-- |
-- | Handles loading and applying themes to the DOM:
-- | - Injects CSS custom properties into document
-- | - Supports loading themes from URLs
-- | - Manages color scheme (light/dark/auto)
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/theme/loader.ts
module Forge.UI.Theme.Loader
  ( applyTheme
  , loadThemeFromUrl
  , getActiveTheme
  , removeTheme
  , setColorScheme
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Forge.UI.Theme.Types (DesktopTheme, ResolvedTheme)
import Forge.UI.Theme.Resolve (resolveThemeVariant, themeToCss)

-- | Style element ID for theme CSS
themeStyleId :: String
themeStyleId = "forge-theme"

-- | Ensure theme style element exists in document head
foreign import ensureLoaderStyleElement :: Effect Unit

-- | Set style element content
foreign import setStyleContent :: String -> Effect Unit

-- | Set document attribute
foreign import setDocumentAttribute :: String -> String -> Effect Unit

-- | Remove document attribute
foreign import removeDocumentAttribute :: String -> Effect Unit

-- | Get document attribute
foreign import getDocumentAttribute :: String -> Effect (Maybe String)

-- | Set document style property
foreign import setDocumentStyleProperty :: String -> String -> Effect Unit

-- | Remove document style property
foreign import removeDocumentStyleProperty :: String -> Effect Unit

-- | Fetch JSON from URL
foreign import fetchJson :: String -> Aff DesktopTheme

-- | Active theme reference
foreign import activeThemeRef :: Effect (Maybe DesktopTheme)
foreign import setActiveThemeRef :: Maybe DesktopTheme -> Effect Unit

-- | Apply a theme to the document
applyTheme :: DesktopTheme -> Maybe String -> Effect Unit
applyTheme theme mThemeId = do
  setActiveThemeRef (Just theme)
  
  let
    lightTokens = resolveThemeVariant theme.light false
    darkTokens = resolveThemeVariant theme.dark true
    targetThemeId = case mThemeId of
      Just id -> id
      Nothing -> theme.id
    css = buildThemeCss lightTokens darkTokens targetThemeId
  
  ensureLoaderStyleElement
  setStyleContent css
  setDocumentAttribute "data-theme" targetThemeId

-- | Build complete CSS with light and dark variants
buildThemeCss :: ResolvedTheme -> ResolvedTheme -> String -> String
buildThemeCss light dark themeId =
  let
    isDefaultTheme = themeId == "forge-1"
    lightCss = themeToCss light
    darkCss = themeToCss dark
  in
    if isDefaultTheme
      then """
:root {
  color-scheme: light;
  --text-mix-blend-mode: multiply;

  """ <> lightCss <> """

  @media (prefers-color-scheme: dark) {
    color-scheme: dark;
    --text-mix-blend-mode: plus-lighter;

    """ <> darkCss <> """
  }
}
"""
      else """
html[data-theme='""" <> themeId <> """'] {
  color-scheme: light;
  --text-mix-blend-mode: multiply;

  """ <> lightCss <> """

  @media (prefers-color-scheme: dark) {
    color-scheme: dark;
    --text-mix-blend-mode: plus-lighter;

    """ <> darkCss <> """
  }
}
"""

-- | Load a theme from a URL
loadThemeFromUrl :: String -> Aff DesktopTheme
loadThemeFromUrl = fetchJson

-- | Get the currently active theme
getActiveTheme :: Effect (Maybe DesktopTheme)
getActiveTheme = do
  mActiveId <- getDocumentAttribute "data-theme"
  mActive <- activeThemeRef
  case mActiveId, mActive of
    Just activeId, Just active | active.id == activeId -> pure (Just active)
    _, _ -> pure Nothing

-- | Remove style element
foreign import removeStyleElement :: Effect Unit

-- | Remove the current theme
removeTheme :: Effect Unit
removeTheme = do
  setActiveThemeRef Nothing
  removeStyleElement
  removeDocumentAttribute "data-theme"

-- | Set the color scheme preference
setColorScheme :: String -> Effect Unit  -- "light" | "dark" | "auto"
setColorScheme scheme =
  if scheme == "auto"
    then removeDocumentStyleProperty "color-scheme"
    else setDocumentStyleProperty "color-scheme" scheme
