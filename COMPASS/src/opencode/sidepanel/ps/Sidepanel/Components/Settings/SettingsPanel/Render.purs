-- | SettingsPanel Render Functions
-- |
-- | Rendering functions for the settings panel component.
-- |
-- | Coeffect Equation:
-- |   Render : State -> H.ComponentHTML Action () m
-- |   with sections: Alerts * Appearance * Keyboard * Features * Storage
-- |
-- | Module Coverage: Header, sections, footer, modals, form elements
module Sidepanel.Components.Settings.SettingsPanel.Render
  ( render
  , renderHeader
  , renderAlertSection
  , renderAppearanceSection
  , renderKeyboardSection
  , renderFeaturesSection
  , renderStorageSection
  , renderFooter
  , renderConfirmResetModal
  , renderConfirmClearModal
  , renderSlider
  , renderToggle
  , renderRadio
  ) where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Data.Int (round)
import Sidepanel.State.Settings (AlertSettings, AppearanceSettings, KeyboardSettings, FeatureSettings, StorageSettings, Theme(..))
import Sidepanel.Components.Settings.SettingsPanel.Types
  ( State
  , Action(..)
  , SliderConfig
  , ToggleConfig
  , parseInt
  , parseFloat
  )

--------------------------------------------------------------------------------
-- | Main Render
--------------------------------------------------------------------------------

-- | Main render function
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

--------------------------------------------------------------------------------
-- | Header
--------------------------------------------------------------------------------

-- | Render header
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

--------------------------------------------------------------------------------
-- | Sections
--------------------------------------------------------------------------------

-- | Render alert settings section
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

-- | Render appearance settings section
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

-- | Render keyboard settings section
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

-- | Render features settings section
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

-- | Render storage settings section
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

--------------------------------------------------------------------------------
-- | Footer
--------------------------------------------------------------------------------

-- | Render footer
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

--------------------------------------------------------------------------------
-- | Modals
--------------------------------------------------------------------------------

-- | Render confirm reset modal
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

-- | Render confirm clear modal
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

--------------------------------------------------------------------------------
-- | Form Elements
--------------------------------------------------------------------------------

-- | Render slider
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

-- | Render toggle
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

-- | Render radio button
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
