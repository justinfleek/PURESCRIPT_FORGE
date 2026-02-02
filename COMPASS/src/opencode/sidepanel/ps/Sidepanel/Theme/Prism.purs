-- | PRISM color system integration for sidepanel theming
-- | Based on PRISM/prism-color-core and spec 47-THEMING.md, 94-FLEEK-CSS-TOKENS.md
module Sidepanel.Theme.Prism where

import Prelude
import Data.Maybe (Maybe)

-- | PRISM color types (from PRISM/prism-color-core)
-- | These will be imported from the PRISM Haskell library via FFI

-- | Theme configuration using PRISM
type PrismThemeConfig =
  { baseHue :: Number           -- [0, 360)
  , baseSaturation :: Number    -- [0, 1]
  , heroHue :: Number           -- [0, 360)
  , heroSaturation :: Number    -- [0, 1]
  , monitorType :: MonitorType
  , blackBalance :: Number      -- [0, 0.20]
  , mode :: ThemeMode
  }

data MonitorType = OLED | LCD
data ThemeMode = Dark | Light

derive instance eqMonitorType :: Eq MonitorType
derive instance eqThemeMode :: Eq ThemeMode

-- | Base16 color palette (from PRISM)
type Base16Colors =
  { base00 :: String  -- Background
  , base01 :: String  -- Lighter background
  , base02 :: String  -- Selection
  , base03 :: String  -- Comments
  , base04 :: String  -- Dark foreground
  , base05 :: String  -- Default foreground
  , base06 :: String  -- Light foreground
  , base07 :: String  -- Brightest
  , base08 :: String  -- Error/Red
  , base09 :: String  -- Warning/Orange
  , base0A :: String  -- Hero accent
  , base0B :: String  -- Success/Green
  , base0C :: String  -- Info/Cyan
  , base0D :: String  -- Link/Blue
  , base0E :: String  -- Special/Purple
  , base0F :: String  -- Deprecated
  }

-- | Fleek brand colors (from spec 94-FLEEK-CSS-TOKENS.md)
type FleekColors =
  { fleekBlue :: String
  , fleekGreen :: String
  , fleekYellow :: String
  , fleekOrange :: String
  }

fleekColors :: FleekColors
fleekColors =
  { fleekBlue: "#0090ff"
  , fleekGreen: "#32e48e"
  , fleekYellow: "#ffe629"
  , fleekOrange: "#f76b15"
  }

-- | Generate theme using PRISM color system
-- | This will call the Haskell PRISM library via FFI
foreign import generatePrismTheme :: PrismThemeConfig -> Base16Colors

-- | Generate Holographic-themed palette (default starting colors)
generateHolographicTheme :: MonitorType -> Base16Colors
generateHolographicTheme monitorType =
  generatePrismTheme
    { baseHue: 260.0      -- Purple base (holographic)
    , baseSaturation: 0.12
    , heroHue: 180.0      -- Cyan hero (iridescent)
    , heroSaturation: 0.85
    , monitorType: monitorType
    , blackBalance: case monitorType of
        OLED -> 0.10
        LCD -> 0.15
    , mode: Dark
    }

-- | Generate Fleek-themed palette (legacy, kept for compatibility)
generateFleekTheme :: MonitorType -> Base16Colors
generateFleekTheme monitorType =
  generatePrismTheme
    { baseHue: 200.0      -- Blue base
    , baseSaturation: 0.5
    , heroHue: 200.0      -- Fleek blue as hero
    , heroSaturation: 1.0
    , monitorType: monitorType
    , blackBalance: case monitorType of
        OLED -> 0.11
        LCD -> 0.16
    , mode: Dark
    }
