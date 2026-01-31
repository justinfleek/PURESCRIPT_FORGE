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
import Argonaut.Core (Json)
import Argonaut.Decode (class DecodeJson, decodeJson, (.:), (.:?))
import Argonaut.Encode (class EncodeJson, encodeJson, (:=), (:=?))
import Argonaut.Parser (jsonParser)
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
      _ -> Left "Invalid theme"

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

-- | JSON codecs for Settings
instance EncodeJson AlertSettings where
  encodeJson s = encodeJson
    { warningPercent: s.warningPercent
    , criticalPercent: s.criticalPercent
    , warningHours: s.warningHours
    , soundEnabled: s.soundEnabled
    }

instance DecodeJson AlertSettings where
  decodeJson json = do
    obj <- decodeJson json
    warningPercent <- obj .: "warningPercent"
    criticalPercent <- obj .: "criticalPercent"
    warningHours <- obj .: "warningHours"
    soundEnabled <- obj .: "soundEnabled"
    pure { warningPercent, criticalPercent, warningHours, soundEnabled }

instance EncodeJson AppearanceSettings where
  encodeJson s = encodeJson { theme: s.theme }

instance DecodeJson AppearanceSettings where
  decodeJson json = do
    obj <- decodeJson json
    theme <- obj .: "theme"
    pure { theme }

instance EncodeJson KeyboardSettings where
  encodeJson s = encodeJson { enabled: s.enabled, vimMode: s.vimMode }

instance DecodeJson KeyboardSettings where
  decodeJson json = do
    obj <- decodeJson json
    enabled <- obj .: "enabled"
    vimMode <- obj .: "vimMode"
    pure { enabled, vimMode }

instance EncodeJson FeatureSettings where
  encodeJson s = encodeJson
    { countdown: s.countdown
    , tokenCharts: s.tokenCharts
    , proofPanel: s.proofPanel
    , timeline: s.timeline
    }

instance DecodeJson FeatureSettings where
  decodeJson json = do
    obj <- decodeJson json
    countdown <- obj .: "countdown"
    tokenCharts <- obj .: "tokenCharts"
    proofPanel <- obj .: "proofPanel"
    timeline <- obj .: "timeline"
    pure { countdown, tokenCharts, proofPanel, timeline }

instance EncodeJson StorageSettings where
  encodeJson s = encodeJson { retentionDays: s.retentionDays }

instance DecodeJson StorageSettings where
  decodeJson json = do
    obj <- decodeJson json
    retentionDays <- obj .: "retentionDays"
    pure { retentionDays }

instance EncodeJson Settings where
  encodeJson s = encodeJson
    { alerts: s.alerts
    , appearance: s.appearance
    , keyboard: s.keyboard
    , features: s.features
    , storage: s.storage
    }

instance DecodeJson Settings where
  decodeJson json = do
    obj <- decodeJson json
    alerts <- obj .: "alerts"
    appearance <- obj .: "appearance"
    keyboard <- obj .: "keyboard"
    features <- obj .: "features"
    storage <- obj .: "storage"
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
encodeSettingsToString = encodeJson >>> show

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
  either (\err -> Left $ "Failed to decode settings: " <> show err) Right $ decodeJson json
