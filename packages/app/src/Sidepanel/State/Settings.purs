-- | Settings Types and Defaults - User Configuration Management
-- |
-- | **What:** Defines all user-configurable settings types with JSON serialization
-- |         support. Provides default values and encoding/decoding functions.
-- | **Why:** Centralizes settings management, ensuring consistent defaults and
-- |         type-safe serialization for persistence.
-- | **How:** Uses Argonaut for JSON encoding/decoding. Settings are persisted to
-- |         localStorage or database and restored on application load.
-- |
-- | **Dependencies:**
-- | - `Argonaut.Core`: JSON representation
-- | - `Argonaut.Encode`/`Decode`: JSON serialization
-- |
-- | **Mathematical Foundation:**
-- | - **Settings Invariants:**
-- |   - `0.0 <= warningPercent <= 1.0` (percentage must be valid)
-- |   - `0.0 <= criticalPercent <= 1.0` (percentage must be valid)
-- |   - `criticalPercent < warningPercent` (critical must be lower than warning)
-- |   - `warningHours >= 0.0` (cannot be negative)
-- |   - `retentionDays >= 0` (cannot be negative)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.State.Settings as Settings
-- |
-- | -- Get default settings
-- | settings :: Settings.Settings
-- | settings = Settings.defaultSettings
-- |
-- | -- Encode to JSON string
-- | jsonString = Settings.encodeSettingsToString settings
-- |
-- | -- Decode from JSON string
-- | case Settings.decodeSettingsFromString jsonString of
-- |   Right settings -> -- Use settings
-- |   Left err -> -- Handle error
-- | ```
-- |
-- | Based on spec 55-SETTINGS-PANEL.md
module Sidepanel.State.Settings where

import Prelude
import Data.Argonaut.Core (Json, stringify)
import Data.Argonaut.Decode (class DecodeJson, decodeJson, (.:))
import Data.Argonaut.Decode.Error (JsonDecodeError(..))
import Data.Argonaut.Encode (class EncodeJson, encodeJson)
import Data.Argonaut.Parser (jsonParser)
import Data.Bifunctor (lmap)
import Data.Either (Either(..), either)

-- | All user-configurable settings - Root settings type
-- |
-- | **Purpose:** Contains all user-configurable settings organized by category.
-- | **Fields:**
-- | - `alerts`: Alert threshold settings
-- | - `appearance`: Appearance settings (theme)
-- | - `keyboard`: Keyboard shortcut settings
-- | - `features`: Feature flags
-- | - `storage`: Storage/retention settings
type Settings =
  { alerts :: AlertSettings
  , appearance :: AppearanceSettings
  , keyboard :: KeyboardSettings
  , features :: FeatureSettings
  , storage :: StorageSettings
  }

type AlertSettings =
  { warningPercent :: Number      -- 0.0-1.0, default 0.20
  , criticalPercent :: Number     -- 0.0-1.0, default 0.05
  , warningHours :: Number        -- Hours, default 2.0
  , soundEnabled :: Boolean       -- Default false
  }

type AppearanceSettings =
  { theme :: Theme
  }

data Theme = Dark | Light | System

derive instance eqTheme :: Eq Theme

instance EncodeJson Theme where
  encodeJson = case _ of
    Dark -> encodeJson "dark"
    Light -> encodeJson "light"
    System -> encodeJson "system"

instance DecodeJson Theme where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "dark" -> pure Dark
      "light" -> pure Light
      "system" -> pure System
      _ -> Left (TypeMismatch "Invalid theme")

type KeyboardSettings =
  { enabled :: Boolean            -- Default true
  , vimMode :: Boolean            -- Default true
  }

type FeatureSettings =
  { countdown :: Boolean          -- Default true
  , tokenCharts :: Boolean        -- Default true
  , proofPanel :: Boolean         -- Default false
  , timeline :: Boolean           -- Default false
  }

type StorageSettings =
  { retentionDays :: Int          -- Default 30
  }

-- | Default settings
defaultSettings :: Settings
defaultSettings =
  { alerts:
      { warningPercent: 0.20
      , criticalPercent: 0.05
      , warningHours: 2.0
      , soundEnabled: false
      }
  , appearance:
      { theme: Dark
      }
  , keyboard:
      { enabled: true
      , vimMode: true
      }
  , features:
      { countdown: true
      , tokenCharts: true
      , proofPanel: false
      , timeline: false
      }
  , storage:
      { retentionDays: 30
      }
  }

-- | Encode AlertSettings to JSON
encodeAlertSettings :: AlertSettings -> Json
encodeAlertSettings s = encodeJson
  { warningPercent: s.warningPercent
  , criticalPercent: s.criticalPercent
  , warningHours: s.warningHours
  , soundEnabled: s.soundEnabled
  }

-- | Decode AlertSettings from JSON
decodeAlertSettings :: Json -> Either JsonDecodeError AlertSettings
decodeAlertSettings json = do
  obj <- decodeJson json
  warningPercent <- obj .: "warningPercent"
  criticalPercent <- obj .: "criticalPercent"
  warningHours <- obj .: "warningHours"
  soundEnabled <- obj .: "soundEnabled"
  pure { warningPercent, criticalPercent, warningHours, soundEnabled }

-- | Encode AppearanceSettings to JSON
encodeAppearanceSettings :: AppearanceSettings -> Json
encodeAppearanceSettings s = encodeJson { theme: s.theme }

-- | Decode AppearanceSettings from JSON
decodeAppearanceSettings :: Json -> Either JsonDecodeError AppearanceSettings
decodeAppearanceSettings json = do
  obj <- decodeJson json
  theme <- obj .: "theme"
  pure { theme }

-- | Encode KeyboardSettings to JSON
encodeKeyboardSettings :: KeyboardSettings -> Json
encodeKeyboardSettings s = encodeJson { enabled: s.enabled, vimMode: s.vimMode }

-- | Decode KeyboardSettings from JSON
decodeKeyboardSettings :: Json -> Either JsonDecodeError KeyboardSettings
decodeKeyboardSettings json = do
  obj <- decodeJson json
  enabled <- obj .: "enabled"
  vimMode <- obj .: "vimMode"
  pure { enabled, vimMode }

-- | Encode FeatureSettings to JSON
encodeFeatureSettings :: FeatureSettings -> Json
encodeFeatureSettings s = encodeJson
  { countdown: s.countdown
  , tokenCharts: s.tokenCharts
  , proofPanel: s.proofPanel
  , timeline: s.timeline
  }

-- | Decode FeatureSettings from JSON
decodeFeatureSettings :: Json -> Either JsonDecodeError FeatureSettings
decodeFeatureSettings json = do
  obj <- decodeJson json
  countdown <- obj .: "countdown"
  tokenCharts <- obj .: "tokenCharts"
  proofPanel <- obj .: "proofPanel"
  timeline <- obj .: "timeline"
  pure { countdown, tokenCharts, proofPanel, timeline }

-- | Encode StorageSettings to JSON
encodeStorageSettings :: StorageSettings -> Json
encodeStorageSettings s = encodeJson { retentionDays: s.retentionDays }

-- | Decode StorageSettings from JSON
decodeStorageSettings :: Json -> Either JsonDecodeError StorageSettings
decodeStorageSettings json = do
  obj <- decodeJson json
  retentionDays <- obj .: "retentionDays"
  pure { retentionDays }

-- | Encode Settings to JSON
encodeSettingsJson :: Settings -> Json
encodeSettingsJson s = encodeJson
  { alerts: encodeAlertSettings s.alerts
  , appearance: encodeAppearanceSettings s.appearance
  , keyboard: encodeKeyboardSettings s.keyboard
  , features: encodeFeatureSettings s.features
  , storage: encodeStorageSettings s.storage
  }

-- | Decode Settings from JSON
decodeSettingsJson :: Json -> Either JsonDecodeError Settings
decodeSettingsJson json = do
  obj <- decodeJson json
  alertsJson <- obj .: "alerts"
  alerts <- decodeAlertSettings alertsJson
  appearanceJson <- obj .: "appearance"
  appearance <- decodeAppearanceSettings appearanceJson
  keyboardJson <- obj .: "keyboard"
  keyboard <- decodeKeyboardSettings keyboardJson
  featuresJson <- obj .: "features"
  features <- decodeFeatureSettings featuresJson
  storageJson <- obj .: "storage"
  storage <- decodeStorageSettings storageJson
  pure { alerts, appearance, keyboard, features, storage }

-- | Encode Settings to JSON string - Serialize settings for persistence
-- |
-- | **Purpose:** Converts Settings to a JSON string for storage (localStorage, database).
-- | **Parameters:**
-- | - `settings`: Settings to encode
-- | **Returns:** JSON string representation
-- | **Side Effects:** None (pure function)
-- |
-- | **Example:**
-- | ```purescript
-- | jsonString = encodeSettingsToString settings
-- | localStorage.setItem "settings" jsonString
-- | ```
encodeSettingsToString :: Settings -> String
encodeSettingsToString = encodeSettingsJson >>> stringify

-- | Decode Settings from JSON string - Deserialize settings from storage
-- |
-- | **Purpose:** Converts a JSON string back to Settings type. Used when loading
-- |             saved settings from localStorage or database.
-- | **Parameters:**
-- | - `str`: JSON string to decode
-- | **Returns:** Either error string or Settings
-- | **Side Effects:** None (pure function)
-- |
-- | **Errors:**
-- | - Returns `Left` with error message if JSON parsing fails
-- | - Returns `Left` with error message if JSON decoding fails
-- |
-- | **Example:**
-- | ```purescript
-- | jsonString <- localStorage.getItem "settings"
-- | case decodeSettingsFromString jsonString of
-- |   Right settings -> -- Use settings
-- |   Left err -> -- Use defaultSettings, handle error
-- | ```
decodeSettingsFromString :: String -> Either String Settings
decodeSettingsFromString str = do
  json <- either Left Right $ jsonParser str
  lmap show $ decodeSettingsJson json
