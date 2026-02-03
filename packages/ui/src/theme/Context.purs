-- | Theme Context - Theme Management and Application
-- |
-- | Provides theme context with:
-- | - Theme selection and switching
-- | - Light/dark mode support
-- | - System preference detection
-- | - Theme preview functionality
-- | - CSS variable generation
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/theme/context.tsx
module Forge.UI.Theme.Context
  ( ThemeContext
  , ThemeProvider
  , useTheme
  , ColorScheme(..)
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Forge.UI.Theme.Types (DesktopTheme, ResolvedTheme)

-- | Color scheme preference
data ColorScheme
  = Light
  | Dark
  | System

derive instance eqColorScheme :: Eq ColorScheme

instance showColorScheme :: Show ColorScheme where
  show Light = "light"
  show Dark = "dark"
  show System = "system"

-- | Theme context interface
type ThemeContext =
  { themeId :: Effect String
  , colorScheme :: Effect ColorScheme
  , mode :: Effect String  -- "light" | "dark"
  , themes :: Effect (Map String DesktopTheme)
  , setTheme :: String -> Effect Unit
  , setColorScheme :: ColorScheme -> Effect Unit
  , registerTheme :: DesktopTheme -> Effect Unit
  , previewTheme :: String -> Effect Unit
  , previewColorScheme :: ColorScheme -> Effect Unit
  , commitPreview :: Effect Unit
  , cancelPreview :: Effect Unit
  }

-- | Storage keys for persistence
storageKeyThemeId :: String
storageKeyThemeId = "forge-theme-id"

storageKeyColorScheme :: String
storageKeyColorScheme = "forge-color-scheme"

storageKeyCssLight :: String
storageKeyCssLight = "forge-theme-css-light"

storageKeyCssDark :: String
storageKeyCssDark = "forge-theme-css-dark"

-- | Internal context reference
foreign import themeContextRef :: Ref (Maybe ThemeContext)

-- | Get system color preference
foreign import getSystemMode :: Effect String

-- | Apply theme CSS to document
foreign import applyThemeCss :: String -> String -> String -> Effect Unit

-- | Store value in localStorage
foreign import setStorageItem :: String -> String -> Effect Unit

-- | Get value from localStorage
foreign import getStorageItem :: String -> Effect (Maybe String)

-- | Theme provider props
type ThemeProviderProps =
  { defaultTheme :: Maybe String
  }

-- | Theme provider component type
type ThemeProvider = ThemeProviderProps -> Effect ThemeContext

-- | Use the theme context
useTheme :: Effect ThemeContext
useTheme = do
  mCtx <- Ref.read themeContextRef
  case mCtx of
    Nothing -> throw "useTheme must be used within a ThemeProvider"
    Just ctx -> pure ctx
