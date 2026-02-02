-- | SettingsPanel Handler
-- |
-- | Action handling for the settings panel component.
-- |
-- | Coeffect Equation:
-- |   Handler : Action -> H.HalogenM State Action () Output m Unit
-- |   with persistence: Settings -o (LocalStorage * Bridge)
-- |
-- | Module Coverage: handleAction, settings persistence
module Sidepanel.Components.Settings.SettingsPanel.Handler
  ( handleAction
  ) where

import Prelude
import Halogen as H
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Sidepanel.State.Settings (Settings, defaultSettings, encodeSettingsToString, decodeSettingsFromString)
import Sidepanel.FFI.LocalStorage as LocalStorage
import Sidepanel.Api.Bridge as Bridge
import Sidepanel.Components.Settings.SettingsPanel.Types
  ( State
  , Action(..)
  , Output(..)
  , Input
  , settingsToSaveRequest
  )

--------------------------------------------------------------------------------
-- | Action Handler
--------------------------------------------------------------------------------

-- | Handle component actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Load settings from localStorage
    stored <- liftEffect $ LocalStorage.getItem "sidepanel.settings"
    case stored >>= decodeSettingsFromString of
      Right loadedSettings -> do
        H.modify_ _ { settings = loadedSettings, originalSettings = loadedSettings }
      Left _ -> do
        pure unit

  Receive input -> do
    H.modify_ _ { settings = input.settings, originalSettings = input.settings, wsClient = input.wsClient }

  SetWarningPercent val ->
    H.modify_ \s -> s 
      { settings = s.settings { alerts = s.settings.alerts { warningPercent = val } }
      , isDirty = true
      }

  SetCriticalPercent val ->
    H.modify_ \s -> s 
      { settings = s.settings { alerts = s.settings.alerts { criticalPercent = val } }
      , isDirty = true
      }

  SetWarningHours val ->
    H.modify_ \s -> s 
      { settings = s.settings { alerts = s.settings.alerts { warningHours = val } }
      , isDirty = true
      }

  ToggleSoundEnabled ->
    H.modify_ \s -> s 
      { settings = s.settings { alerts = s.settings.alerts { soundEnabled = not s.settings.alerts.soundEnabled } }
      , isDirty = true
      }

  SetTheme theme ->
    H.modify_ \s -> s 
      { settings = s.settings { appearance = s.settings.appearance { theme = theme } }
      , isDirty = true
      }

  ToggleKeyboardEnabled ->
    H.modify_ \s -> s 
      { settings = s.settings { keyboard = s.settings.keyboard { enabled = not s.settings.keyboard.enabled } }
      , isDirty = true
      }

  ToggleVimMode ->
    H.modify_ \s -> s 
      { settings = s.settings { keyboard = s.settings.keyboard { vimMode = not s.settings.keyboard.vimMode } }
      , isDirty = true
      }

  ToggleFeature featureName ->
    H.modify_ \s ->
      let
        features = s.settings.features
        newFeatures = case featureName of
          "countdown" -> features { countdown = not features.countdown }
          "tokenCharts" -> features { tokenCharts = not features.tokenCharts }
          "proofPanel" -> features { proofPanel = not features.proofPanel }
          "timeline" -> features { timeline = not features.timeline }
          _ -> features
      in
        s { settings = s.settings { features = newFeatures }
          , isDirty = true
          }

  SetRetentionDays days ->
    H.modify_ \s -> s 
      { settings = s.settings { storage = s.settings.storage { retentionDays = days } }
      , isDirty = true
      }

  ConfirmClearData ->
    H.modify_ _ { showConfirmClear = true }

  ClearAllData -> do
    H.modify_ _ { showConfirmClear = false }
    H.raise DataCleared

  CancelClear ->
    H.modify_ _ { showConfirmClear = false }

  Save -> do
    H.modify_ _ { isSaving = true }
    state <- H.get
    let settings = state.settings
    -- Save to localStorage
    liftEffect $ LocalStorage.setItem "sidepanel.settings" (encodeSettingsToString settings)
    -- Sync to bridge server
    case state.wsClient of
      Just client -> do
        let saveRequest = settingsToSaveRequest settings
        result <- H.liftAff $ Bridge.saveSettings client saveRequest
        case result of
          Right response -> pure unit
          Left err -> pure unit
      Nothing -> pure unit
    H.modify_ _ { isSaving = false, isDirty = false, originalSettings = settings }
    H.raise (SettingsChanged settings)

  ResetToDefaults -> do
    H.modify_ \s -> s 
      { settings = defaultSettings
      , originalSettings = defaultSettings
      , isDirty = false
      , showConfirmReset = false
      }
    settings <- H.gets _.settings
    H.raise (SettingsChanged settings)

  ConfirmReset ->
    H.modify_ _ { showConfirmReset = true }

  CancelReset ->
    H.modify_ _ { showConfirmReset = false }
