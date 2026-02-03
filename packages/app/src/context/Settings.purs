-- | Settings context - manages user preferences
-- | Migrated from: forge-dev/packages/app/src/context/settings.tsx
module App.Context.Settings
  ( Settings
  , NotificationSettings
  , SoundSettings
  , GeneralSettings
  , UpdateSettings
  , AppearanceSettings
  , PermissionSettings
  , defaultSettings
  , monoFontFamily
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)

-- | Notification settings
type NotificationSettings =
  { agent :: Boolean
  , permissions :: Boolean
  , errors :: Boolean
  }

-- | Sound settings
type SoundSettings =
  { agent :: String
  , permissions :: String
  , errors :: String
  }

-- | General settings
type GeneralSettings =
  { autoSave :: Boolean
  , releaseNotes :: Boolean
  }

-- | Update settings
type UpdateSettings =
  { startup :: Boolean
  }

-- | Appearance settings
type AppearanceSettings =
  { fontSize :: Int
  , font :: String
  }

-- | Permission settings
type PermissionSettings =
  { autoApprove :: Boolean
  }

-- | Complete settings record
type Settings =
  { general :: GeneralSettings
  , updates :: UpdateSettings
  , appearance :: AppearanceSettings
  , keybinds :: Map String String
  , permissions :: PermissionSettings
  , notifications :: NotificationSettings
  , sounds :: SoundSettings
  }

-- | Default settings values
defaultSettings :: Settings
defaultSettings =
  { general:
      { autoSave: true
      , releaseNotes: true
      }
  , updates:
      { startup: true
      }
  , appearance:
      { fontSize: 14
      , font: "ibm-plex-mono"
      }
  , keybinds: Map.empty
  , permissions:
      { autoApprove: false
      }
  , notifications:
      { agent: true
      , permissions: true
      , errors: false
      }
  , sounds:
      { agent: "staplebops-01"
      , permissions: "staplebops-02"
      , errors: "nope-03"
      }
  }

-- | Monospace font fallback
monoFallback :: String
monoFallback = 
  "ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, \"Liberation Mono\", \"Courier New\", monospace"

-- | Font family mappings for monospace fonts
monoFonts :: Map String String
monoFonts = Map.fromFoldable
  [ "ibm-plex-mono" /\ ("\"IBM Plex Mono\", \"IBM Plex Mono Fallback\", " <> monoFallback)
  , "cascadia-code" /\ ("\"Cascadia Code Nerd Font\", \"Cascadia Code NF\", \"Cascadia Mono NF\", \"IBM Plex Mono\", \"IBM Plex Mono Fallback\", " <> monoFallback)
  , "fira-code" /\ ("\"Fira Code Nerd Font\", \"FiraMono Nerd Font\", \"FiraMono Nerd Font Mono\", \"IBM Plex Mono\", \"IBM Plex Mono Fallback\", " <> monoFallback)
  , "hack" /\ ("\"Hack Nerd Font\", \"Hack Nerd Font Mono\", \"IBM Plex Mono\", \"IBM Plex Mono Fallback\", " <> monoFallback)
  , "inconsolata" /\ ("\"Inconsolata Nerd Font\", \"Inconsolata Nerd Font Mono\", \"IBM Plex Mono\", \"IBM Plex Mono Fallback\", " <> monoFallback)
  , "intel-one-mono" /\ ("\"Intel One Mono Nerd Font\", \"IntoneMono Nerd Font\", \"IntoneMono Nerd Font Mono\", \"IBM Plex Mono\", \"IBM Plex Mono Fallback\", " <> monoFallback)
  , "iosevka" /\ ("\"Iosevka Nerd Font\", \"Iosevka Nerd Font Mono\", \"IBM Plex Mono\", \"IBM Plex Mono Fallback\", " <> monoFallback)
  , "jetbrains-mono" /\ ("\"JetBrains Mono Nerd Font\", \"JetBrainsMono Nerd Font Mono\", \"JetBrainsMonoNL Nerd Font\", \"JetBrainsMonoNL Nerd Font Mono\", \"IBM Plex Mono\", \"IBM Plex Mono Fallback\", " <> monoFallback)
  , "meslo-lgs" /\ ("\"Meslo LGS Nerd Font\", \"MesloLGS Nerd Font\", \"MesloLGM Nerd Font\", \"IBM Plex Mono\", \"IBM Plex Mono Fallback\", " <> monoFallback)
  , "roboto-mono" /\ ("\"Roboto Mono Nerd Font\", \"RobotoMono Nerd Font\", \"RobotoMono Nerd Font Mono\", \"IBM Plex Mono\", \"IBM Plex Mono Fallback\", " <> monoFallback)
  , "source-code-pro" /\ ("\"Source Code Pro Nerd Font\", \"SauceCodePro Nerd Font\", \"SauceCodePro Nerd Font Mono\", \"IBM Plex Mono\", \"IBM Plex Mono Fallback\", " <> monoFallback)
  , "ubuntu-mono" /\ ("\"Ubuntu Mono Nerd Font\", \"UbuntuMono Nerd Font\", \"UbuntuMono Nerd Font Mono\", \"IBM Plex Mono\", \"IBM Plex Mono Fallback\", " <> monoFallback)
  ]

-- | Get monospace font family CSS value
monoFontFamily :: Maybe String -> String
monoFontFamily mFont =
  let font = fromMaybe defaultSettings.appearance.font mFont
      defaultFont = fromMaybe "" (Map.lookup defaultSettings.appearance.font monoFonts)
  in fromMaybe defaultFont (Map.lookup font monoFonts)
