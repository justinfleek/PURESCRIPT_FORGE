-- | SettingsPanel Types
-- |
-- | Type definitions for the settings panel component.
-- |
-- | Coeffect Equation:
-- |   Types : Settings -> State -> Action -> Output
-- |   with persistence: Settings -o LocalStorage * Bridge
-- |
-- | Module Coverage: State, Action, Output, Input, helper types
module Sidepanel.Components.Settings.SettingsPanel.Types
  ( -- * Component Types
    State
  , Action(..)
  , Output(..)
  , Input
    -- * Helper Types
  , SliderConfig
  , ToggleConfig
    -- * Initial State
  , initialState
    -- * Helpers
  , settingsToSaveRequest
  , parseInt
  , parseFloat
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Int (floor)
import Data.Number (fromString)
import Sidepanel.State.Settings (Settings, Theme(..))
import Sidepanel.WebSocket.Client as WS
import Sidepanel.Api.Bridge as Bridge

--------------------------------------------------------------------------------
-- | Component Types
--------------------------------------------------------------------------------

-- | Component state
type State =
  { settings :: Settings
  , originalSettings :: Settings
  , isDirty :: Boolean
  , isSaving :: Boolean
  , showConfirmReset :: Boolean
  , showConfirmClear :: Boolean
  , wsClient :: Maybe WS.WSClient
  }

-- | Actions
data Action
  = Initialize
  | Receive Input
  | SetWarningPercent Number
  | SetCriticalPercent Number
  | SetWarningHours Number
  | ToggleSoundEnabled
  | SetTheme Theme
  | ToggleKeyboardEnabled
  | ToggleVimMode
  | ToggleFeature String
  | SetRetentionDays Int
  | ConfirmClearData
  | ClearAllData
  | CancelClear
  | Save
  | ResetToDefaults
  | ConfirmReset
  | CancelReset

-- | Output
data Output
  = SettingsChanged Settings
  | DataCleared

-- | Component input
type Input = { settings :: Settings, wsClient :: Maybe WS.WSClient }

--------------------------------------------------------------------------------
-- | Helper Types
--------------------------------------------------------------------------------

-- | Slider configuration
type SliderConfig =
  { label :: String
  , description :: String
  , value :: Number
  , min :: Number
  , max :: Number
  , step :: Number
  , format :: Number -> String
  , onChange :: Number -> Action
  }

-- | Toggle configuration
type ToggleConfig =
  { label :: String
  , checked :: Boolean
  , onChange :: Action
  , disabled :: Boolean
  }

--------------------------------------------------------------------------------
-- | Initial State
--------------------------------------------------------------------------------

-- | Initialize state from input
initialState :: Input -> State
initialState input =
  { settings: input.settings
  , originalSettings: input.settings
  , isDirty: false
  , isSaving: false
  , showConfirmReset: false
  , showConfirmClear: false
  , wsClient: input.wsClient
  }

--------------------------------------------------------------------------------
-- | Helpers
--------------------------------------------------------------------------------

-- | Convert Settings to SettingsSaveRequest for bridge API
settingsToSaveRequest :: Settings -> Bridge.SettingsSaveRequest
settingsToSaveRequest s =
  { alerts:
      { warningPercent: s.alerts.warningPercent
      , criticalPercent: s.alerts.criticalPercent
      , warningHours: s.alerts.warningHours
      , soundEnabled: s.alerts.soundEnabled
      }
  , appearance:
      { theme: themeToString s.appearance.theme
      }
  , keyboard:
      { enabled: s.keyboard.enabled
      , vimMode: s.keyboard.vimMode
      }
  , features:
      { countdown: s.features.countdown
      , tokenCharts: s.features.tokenCharts
      , proofPanel: s.features.proofPanel
      , timeline: s.features.timeline
      }
  , storage:
      { retentionDays: s.storage.retentionDays
      }
  }
  where
    themeToString :: Theme -> String
    themeToString = case _ of
      Dark -> "dark"
      Light -> "light"
      System -> "system"

-- | Parse integer from string
parseInt :: String -> Int
parseInt s = case fromString s of
  Just n -> floor n
  Nothing -> 30

-- | Parse float from string
parseFloat :: String -> Number
parseFloat s = case fromString s of
  Just n -> n
  Nothing -> 0.0
