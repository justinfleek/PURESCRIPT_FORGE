-- | Settings Panel Component - Application Settings Management
-- |
-- | **What:** Provides a comprehensive settings interface for configuring alerts, appearance,
-- |         keyboard shortcuts, features, and storage. Supports saving settings to localStorage
-- |         and syncing to Bridge Server.
-- | **Why:** Enables users to customize their sidepanel experience, configure alert thresholds,
-- |         choose themes, enable/disable features, and manage data retention.
-- | **How:** Renders settings sections with sliders, toggles, radio buttons, and dropdowns.
-- |         Tracks dirty state and provides save/reset functionality. Persists to localStorage
-- |         and syncs to Bridge Server via WebSocket.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.Settings`: Settings types and encoding/decoding
-- | - `Sidepanel.FFI.LocalStorage`: Local persistence
-- | - `Sidepanel.WebSocket.Client`: WebSocket communication
-- | - `Sidepanel.Api.Bridge`: Bridge API methods for settings sync
-- |
-- | **Mathematical Foundation:**
-- | - **Dirty State:** Settings are marked dirty when they differ from `originalSettings`.
-- |   Dirty state is calculated on each change.
-- | - **Settings Sync:** Settings are saved to localStorage immediately and synced to Bridge
-- |   Server via `settings.save` method.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Settings.SettingsPanel as SettingsPanel
-- |
-- | -- In parent component:
-- | HH.slot _settings unit SettingsPanel.component
-- |   { settings: appState.settings, wsClient: wsClient }
-- |   (case _ of
-- |     SettingsPanel.SettingsChanged newSettings -> HandleSettingsChanged newSettings
-- |     SettingsPanel.DataCleared -> HandleDataCleared)
-- | ```
-- |
-- | Based on spec 55-SETTINGS-PANEL.md
module Sidepanel.Components.Settings.SettingsPanel where

import Prelude
import Data.Maybe (Maybe(..), fromMaybe)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Sidepanel.State.Settings (Settings, AlertSettings, AppearanceSettings, KeyboardSettings, FeatureSettings, StorageSettings, Theme(..), defaultSettings, encodeSettingsToString, decodeSettingsFromString)
import Sidepanel.FFI.LocalStorage as LocalStorage
import Sidepanel.WebSocket.Client as WS
import Sidepanel.Api.Bridge as Bridge

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

-- | Component
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      , initialize = Just Initialize
      }
  }

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

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "settings-panel") ]
    [ renderHeader state
    , renderAlertSection state.settings.alerts
    , renderAppearanceSection state.settings.appearance
    , renderKeyboardSection state.settings.keyboard
    , renderFeaturesSection state.settings.features
    , renderStorageSection state.settings.storage
    , renderFooter state
    , if state.showConfirmReset then renderConfirmResetModal else HH.text ""
    , if state.showConfirmClear then renderConfirmClearModal else HH.text ""
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.header
    [ HP.class_ (H.ClassName "settings-panel__header") ]
    [ HH.h2_ [ HH.text "Settings" ]
    , if state.isDirty then
        HH.span
          [ HP.class_ (H.ClassName "settings-panel__dirty-indicator") ]
          [ HH.text "Unsaved changes" ]
      else
        HH.text ""
    ]

renderAlertSection :: forall m. AlertSettings -> H.ComponentHTML Action () m
renderAlertSection alerts =
  HH.section
    [ HP.class_ (H.ClassName "settings-section") ]
    [ HH.h3 [ HP.class_ (H.ClassName "settings-section__title") ]
        [ HH.text "Alerts" ]
    , renderSlider
        { label: "Warning threshold"
        , description: "Show warning when balance drops below"
        , value: alerts.warningPercent
        , min: 0.05
        , max: 0.50
        , step: 0.05
        , format: \v -> show (round (v * 100.0)) <> "%"
        , onChange: SetWarningPercent
        }
    , renderSlider
        { label: "Critical threshold"
        , description: "Show critical alert when balance drops below"
        , value: alerts.criticalPercent
        , min: 0.01
        , max: 0.20
        , step: 0.01
        , format: \v -> show (round (v * 100.0)) <> "%"
        , onChange: SetCriticalPercent
        }
    , renderSlider
        { label: "Time-based warning"
        , description: "Warn when less than N hours until depletion"
        , value: alerts.warningHours
        , min: 0.5
        , max: 8.0
        , step: 0.5
        , format: \v -> show v <> "h"
        , onChange: SetWarningHours
        }
    , renderToggle
        { label: "Enable sound alerts"
        , checked: alerts.soundEnabled
        , onChange: ToggleSoundEnabled
        , disabled: false
        }
    ]

renderAppearanceSection :: forall m. AppearanceSettings -> H.ComponentHTML Action () m
renderAppearanceSection appearance =
  HH.section
    [ HP.class_ (H.ClassName "settings-section") ]
    [ HH.h3 [ HP.class_ (H.ClassName "settings-section__title") ]
        [ HH.text "Appearance" ]
    , HH.div
        [ HP.class_ (H.ClassName "settings-row") ]
        [ HH.span [ HP.class_ (H.ClassName "settings-label") ]
            [ HH.text "Theme" ]
        , HH.div
            [ HP.class_ (H.ClassName "radio-group") ]
            [ renderRadio "theme" "Dark" (appearance.theme == Dark) (SetTheme Dark)
            , renderRadio "theme" "Light" (appearance.theme == Light) (SetTheme Light)
            , renderRadio "theme" "System" (appearance.theme == System) (SetTheme System)
            ]
        ]
    ]

renderKeyboardSection :: forall m. KeyboardSettings -> H.ComponentHTML Action () m
renderKeyboardSection keyboard =
  HH.section
    [ HP.class_ (H.ClassName "settings-section") ]
    [ HH.h3 [ HP.class_ (H.ClassName "settings-section__title") ]
        [ HH.text "Keyboard" ]
    , renderToggle
        { label: "Enable keyboard shortcuts"
        , checked: keyboard.enabled
        , onChange: ToggleKeyboardEnabled
        , disabled: false
        }
    , renderToggle
        { label: "Vim-style navigation"
        , checked: keyboard.vimMode
        , onChange: ToggleVimMode
        , disabled: not keyboard.enabled
        }
    ]

renderFeaturesSection :: forall m. FeatureSettings -> H.ComponentHTML Action () m
renderFeaturesSection features =
  HH.section
    [ HP.class_ (H.ClassName "settings-section") ]
    [ HH.h3 [ HP.class_ (H.ClassName "settings-section__title") ]
        [ HH.text "Features" ]
    , renderToggle
        { label: "Countdown timer"
        , checked: features.countdown
        , onChange: ToggleFeature "countdown"
        , disabled: false
        }
    , renderToggle
        { label: "Token usage charts"
        , checked: features.tokenCharts
        , onChange: ToggleFeature "tokenCharts"
        , disabled: false
        }
    , renderToggle
        { label: "Proof panel (requires Lean4)"
        , checked: features.proofPanel
        , onChange: ToggleFeature "proofPanel"
        , disabled: false
        }
    , renderToggle
        { label: "Timeline / snapshots"
        , checked: features.timeline
        , onChange: ToggleFeature "timeline"
        , disabled: false
        }
    ]

renderStorageSection :: forall m. StorageSettings -> H.ComponentHTML Action () m
renderStorageSection storage =
  HH.section
    [ HP.class_ (H.ClassName "settings-section") ]
    [ HH.h3 [ HP.class_ (H.ClassName "settings-section__title") ]
        [ HH.text "Storage" ]
    , HH.div
        [ HP.class_ (H.ClassName "settings-row") ]
        [ HH.span [ HP.class_ (H.ClassName "settings-label") ]
            [ HH.text "Session retention" ]
        , HH.select
            [ HP.class_ (H.ClassName "settings-select")
            , HE.onValueChange \v -> SetRetentionDays (parseInt v)
            ]
            [ HH.option [ HP.value "7", HP.selected (storage.retentionDays == 7) ]
                [ HH.text "7 days" ]
            , HH.option [ HP.value "14", HP.selected (storage.retentionDays == 14) ]
                [ HH.text "14 days" ]
            , HH.option [ HP.value "30", HP.selected (storage.retentionDays == 30) ]
                [ HH.text "30 days" ]
            , HH.option [ HP.value "90", HP.selected (storage.retentionDays == 90) ]
                [ HH.text "90 days" ]
            ]
        ]
    , HH.button
        [ HP.classes [ H.ClassName "btn", H.ClassName "btn--danger", H.ClassName "btn--outline" ]
        , HE.onClick \_ -> ConfirmClearData
        ]
        [ HH.text "Clear All Data" ]
    ]

renderFooter :: forall m. State -> H.ComponentHTML Action () m
renderFooter state =
  HH.footer
    [ HP.class_ (H.ClassName "settings-panel__footer") ]
    [ HH.span [ HP.class_ (H.ClassName "settings-version") ]
        [ HH.text "Version 0.1.0" ]
    , HH.div
        [ HP.class_ (H.ClassName "settings-actions") ]
        [ HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--ghost" ]
            , HE.onClick \_ -> ConfirmReset
            ]
            [ HH.text "Reset to Defaults" ]
        , if state.isDirty then
            HH.button
              [ HP.classes [ H.ClassName "btn", H.ClassName "btn--primary" ]
              , HP.disabled state.isSaving
              , HE.onClick \_ -> Save
              ]
              [ HH.text $ if state.isSaving then "Saving..." else "Save Changes" ]
          else
            HH.text ""
        ]
    ]

renderConfirmResetModal :: forall m. H.ComponentHTML Action () m
renderConfirmResetModal =
  HH.div
    [ HP.class_ (H.ClassName "modal") ]
    [ HH.div [ HP.class_ (H.ClassName "modal__content") ]
        [ HH.h3_ [ HH.text "Reset to Defaults?" ]
        , HH.p_ [ HH.text "This will reset all settings to their default values." ]
        , HH.div [ HP.class_ (H.ClassName "modal__actions") ]
            [ HH.button
                [ HP.classes [ H.ClassName "btn", H.ClassName "btn--ghost" ]
                , HE.onClick \_ -> CancelReset
                ]
                [ HH.text "Cancel" ]
            , HH.button
                [ HP.classes [ H.ClassName "btn", H.ClassName "btn--primary" ]
                , HE.onClick \_ -> ResetToDefaults
                ]
                [ HH.text "Reset" ]
            ]
        ]
    ]

renderConfirmClearModal :: forall m. H.ComponentHTML Action () m
renderConfirmClearModal =
  HH.div
    [ HP.class_ (H.ClassName "modal") ]
    [ HH.div [ HP.class_ (H.ClassName "modal__content") ]
        [ HH.h3_ [ HH.text "Clear All Data?" ]
        , HH.p_ [ HH.text "This will permanently delete all session history and snapshots." ]
        , HH.div [ HP.class_ (H.ClassName "modal__actions") ]
            [ HH.button
                [ HP.classes [ H.ClassName "btn", H.ClassName "btn--ghost" ]
                , HE.onClick \_ -> CancelClear
                ]
                [ HH.text "Cancel" ]
            , HH.button
                [ HP.classes [ H.ClassName "btn", H.ClassName "btn--danger" ]
                , HE.onClick \_ -> ClearAllData
                ]
                [ HH.text "Clear" ]
            ]
        ]
    ]

-- Helper types
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

type ToggleConfig =
  { label :: String
  , checked :: Boolean
  , onChange :: Action
  , disabled :: Boolean
  }

renderSlider :: forall m. SliderConfig -> H.ComponentHTML Action () m
renderSlider config =
  HH.div
    [ HP.class_ (H.ClassName "settings-row settings-row--slider") ]
    [ HH.div
        [ HP.class_ (H.ClassName "settings-label-group") ]
        [ HH.span [ HP.class_ (H.ClassName "settings-label") ]
            [ HH.text config.label ]
        , HH.span [ HP.class_ (H.ClassName "settings-description") ]
            [ HH.text config.description ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "slider-container") ]
        [ HH.input
            [ HP.type_ HP.InputRange
            , HP.class_ (H.ClassName "slider")
            , HP.value (show config.value)
            , HP.min (show config.min)
            , HP.max (show config.max)
            , HP.step (show config.step)
            , HE.onValueChange \v -> config.onChange (parseFloat v)
            ]
        , HH.span [ HP.class_ (H.ClassName "slider-value") ]
            [ HH.text (config.format config.value) ]
        ]
    ]

renderToggle :: forall m. ToggleConfig -> H.ComponentHTML Action () m
renderToggle config =
  HH.label
    [ HP.classes
        [ H.ClassName "settings-toggle"
        , if config.disabled then H.ClassName "settings-toggle--disabled" else H.ClassName ""
        ]
    ]
    [ HH.input
        [ HP.type_ HP.InputCheckbox
        , HP.checked config.checked
        , HP.disabled config.disabled
        , HE.onChecked \_ -> config.onChange
        ]
    , HH.span [ HP.class_ (H.ClassName "toggle-label") ]
        [ HH.text config.label ]
    ]

renderRadio :: forall m. String -> String -> Boolean -> Action -> H.ComponentHTML Action () m
renderRadio name value checked action =
  HH.label
    [ HP.class_ (H.ClassName "radio-option") ]
    [ HH.input
        [ HP.type_ HP.InputRadio
        , HP.name name
        , HP.value value
        , HP.checked checked
        , HE.onChecked \_ -> action
        ]
    , HH.span_ [ HH.text value ]
    ]

-- Helper functions
parseInt :: String -> Int
parseInt s = case parseFloat s of
  Just n -> floor n
  Nothing -> 30

parseFloat :: String -> Number
parseFloat s = case fromString s of
  Just n -> n
  Nothing -> 0.0

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive newSettings ->
    H.modify_ \s ->
      s { settings = newSettings
        , originalSettings = newSettings
        , isDirty = false
        }

  SetWarningPercent val ->
    H.modify_ \s ->
      s { settings = s.settings { alerts = s.settings.alerts { warningPercent = val } }
        , isDirty = s.settings.alerts.warningPercent /= val
        }

  SetCriticalPercent val ->
    H.modify_ \s ->
      s { settings = s.settings { alerts = s.settings.alerts { criticalPercent = val } }
        , isDirty = s.settings.alerts.criticalPercent /= val
        }

  SetWarningHours val ->
    H.modify_ \s ->
      s { settings = s.settings { alerts = s.settings.alerts { warningHours = val } }
        , isDirty = s.settings.alerts.warningHours /= val
        }

  ToggleSoundEnabled ->
    H.modify_ \s ->
      s { settings = s.settings { alerts = s.settings.alerts { soundEnabled = not s.settings.alerts.soundEnabled } }
        , isDirty = s.settings.alerts.soundEnabled == s.originalSettings.alerts.soundEnabled
        }

  SetTheme theme ->
    H.modify_ \s ->
      s { settings = s.settings { appearance = s.settings.appearance { theme = theme } }
        , isDirty = s.settings.appearance.theme /= s.originalSettings.appearance.theme
        }

  ToggleKeyboardEnabled ->
    H.modify_ \s ->
      s { settings = s.settings { keyboard = s.settings.keyboard { enabled = not s.settings.keyboard.enabled } }
        , isDirty = s.settings.keyboard.enabled == s.originalSettings.keyboard.enabled
        }

  ToggleVimMode ->
    H.modify_ \s ->
      s { settings = s.settings { keyboard = s.settings.keyboard { vimMode = not s.settings.keyboard.vimMode } }
        , isDirty = s.settings.keyboard.vimMode == s.originalSettings.keyboard.vimMode
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
          , isDirty = newFeatures /= s.originalSettings.features
          }

  SetRetentionDays days ->
    H.modify_ \s ->
      s { settings = s.settings { storage = s.settings.storage { retentionDays = days } }
        , isDirty = s.settings.storage.retentionDays /= s.originalSettings.storage.retentionDays
        }

  ConfirmClearData ->
    H.modify_ _ { showConfirmClear = true }

  ClearAllData -> do
    H.modify_ _ { showConfirmClear = false }
    H.raise DataCleared

  CancelClear ->
    H.modify_ _ { showConfirmClear = false }

  Initialize -> do
    -- Load settings from localStorage
    stored <- liftEffect $ LocalStorage.getItem "sidepanel.settings"
    case stored >>= decodeSettingsFromString of
      Right loadedSettings -> do
        H.modify_ _ { settings = loadedSettings, originalSettings = loadedSettings }
      Left _ -> do
        -- Use default settings if loading fails
        pure unit

  Receive input -> do
    H.modify_ _ { settings = input.settings, originalSettings = input.settings, wsClient = input.wsClient }

  Save -> do
    H.modify_ _ { isSaving = true }
    state <- H.get
    let settings = state.settings
    -- Save to localStorage
    liftEffect $ LocalStorage.setItem "sidepanel.settings" (encodeSettingsToString settings)
    -- Sync to bridge server via settings.save method
    case state.wsClient of
      Just client -> do
        let saveRequest = settingsToSaveRequest settings
        result <- H.liftAff $ Bridge.saveSettings client saveRequest
        case result of
          Right response -> do
            if response.success then
              pure unit  -- Success
            else
              pure unit  -- Handle error (could show notification)
          Left err -> pure unit  -- Handle error (could show notification)
      Nothing -> pure unit
    H.modify_ _ { isSaving = false, isDirty = false, originalSettings = settings }
    H.raise (SettingsChanged settings)

  ResetToDefaults -> do
    H.modify_ \s ->
      s { settings = defaultSettings
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

-- Helper imports
import Data.Int (floor)
import Data.Number (fromString)
