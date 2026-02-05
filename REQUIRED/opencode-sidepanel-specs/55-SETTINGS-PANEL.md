# 55-SETTINGS-PANEL: User Preferences Configuration

## Overview

The Settings Panel allows users to configure alerts, keyboard shortcuts, theme, and feature toggles. Settings persist across sessions via localStorage and sync to the bridge.

---

## Visual Design

### Settings Layout

```
┌─────────────────────────────────────────────────────────────────────────┐
│  SETTINGS                                                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ALERTS                                                                  │
│  ────────────────────────────────────────────────────────────────────   │
│                                                                          │
│  Warning threshold        ┌──────────────────────────────┐              │
│  Show warning when        │ ████████░░░░░░░░░░  20%     │              │
│  balance drops below      └──────────────────────────────┘              │
│                                                                          │
│  Critical threshold       ┌──────────────────────────────┐              │
│  Show critical when       │ ██░░░░░░░░░░░░░░░░  5%      │              │
│  balance drops below      └──────────────────────────────┘              │
│                                                                          │
│  Time-based warning       ┌──────────────────────────────┐              │
│  Warn when < hours        │ ████████░░░░░░░░░░  2h      │              │
│  until depletion          └──────────────────────────────┘              │
│                                                                          │
│  □ Enable sound alerts                                                  │
│                                                                          │
│  APPEARANCE                                                              │
│  ────────────────────────────────────────────────────────────────────   │
│                                                                          │
│  Theme                    ◉ Dark  ○ Light  ○ System                    │
│                                                                          │
│  KEYBOARD                                                                │
│  ────────────────────────────────────────────────────────────────────   │
│                                                                          │
│  ☑ Enable keyboard shortcuts                                            │
│  ☑ Vim-style navigation                                                 │
│                                                                          │
│  FEATURES                                                                │
│  ────────────────────────────────────────────────────────────────────   │
│                                                                          │
│  ☑ Countdown timer                                                      │
│  ☑ Token usage charts                                                   │
│  □ Proof panel (requires Lean4)                                         │
│  □ Timeline / snapshots                                                 │
│                                                                          │
│  STORAGE                                                                 │
│  ────────────────────────────────────────────────────────────────────   │
│                                                                          │
│  Session retention        ┌─────────────┐                               │
│                           │ 30 days   ▼│                               │
│                           └─────────────┘                               │
│                                                                          │
│  [Clear All Data]                                                        │
│                                                                          │
│  ────────────────────────────────────────────────────────────────────   │
│  Version 0.1.0                               [Reset to Defaults]        │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Settings Schema

```purescript
module Sidepanel.State.Settings where

import Prelude

-- All user-configurable settings
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

-- Default settings
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
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.Settings.SettingsPanel where

import Prelude
import Data.Maybe (Maybe(..))
import Sidepanel.State.Settings

-- Component state
type State =
  { settings :: Settings
  , originalSettings :: Settings  -- For detecting changes
  , isDirty :: Boolean
  , isSaving :: Boolean
  , showConfirmReset :: Boolean
  , showConfirmClear :: Boolean
  }

-- Actions
data Action
  = Initialize
  | Receive Settings
  
  -- Alerts
  | SetWarningPercent Number
  | SetCriticalPercent Number
  | SetWarningHours Number
  | ToggleSoundEnabled
  
  -- Appearance
  | SetTheme Theme
  
  -- Keyboard
  | ToggleKeyboardEnabled
  | ToggleVimMode
  
  -- Features
  | ToggleFeature String
  
  -- Storage
  | SetRetentionDays Int
  | ConfirmClearData
  | ClearAllData
  | CancelClear
  
  -- Actions
  | Save
  | ResetToDefaults
  | ConfirmReset
  | CancelReset

-- Output
data Output
  = SettingsChanged Settings
  | DataCleared
```

### Component

```purescript
component :: forall q m. MonadAff m => H.Component q Settings Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      }
  }

initialState :: Settings -> State
initialState settings =
  { settings
  , originalSettings: settings
  , isDirty: false
  , isSaving: false
  , showConfirmReset: false
  , showConfirmClear: false
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
    
    -- Confirmation modals
    , when state.showConfirmReset (renderConfirmResetModal)
    , when state.showConfirmClear (renderConfirmClearModal)
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.header
    [ HP.class_ (H.ClassName "settings-panel__header") ]
    [ HH.h2_ [ HH.text "Settings" ]
    , when state.isDirty $
        HH.span 
          [ HP.class_ (H.ClassName "settings-panel__dirty-indicator") ]
          [ HH.text "Unsaved changes" ]
    ]

renderAlertSection :: forall m. AlertSettings -> H.ComponentHTML Action () m
renderAlertSection alerts =
  HH.section
    [ HP.class_ (H.ClassName "settings-section") ]
    [ HH.h3 [ HP.class_ (H.ClassName "settings-section__title") ] 
        [ HH.text "Alerts" ]
    
    -- Warning threshold slider
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
    
    -- Critical threshold slider
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
    
    -- Time-based warning slider
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
    
    -- Sound toggle
    , renderToggle
        { label: "Enable sound alerts"
        , checked: alerts.soundEnabled
        , onChange: ToggleSoundEnabled
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
        }
    
    , renderToggle
        { label: "Token usage charts"
        , checked: features.tokenCharts
        , onChange: ToggleFeature "tokenCharts"
        }
    
    , renderToggle
        { label: "Proof panel (requires Lean4)"
        , checked: features.proofPanel
        , onChange: ToggleFeature "proofPanel"
        }
    
    , renderToggle
        { label: "Timeline / snapshots"
        , checked: features.timeline
        , onChange: ToggleFeature "timeline"
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
            , HE.onValueChange (SetRetentionDays <<< parseInt)
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
        , when state.isDirty $
            HH.button
              [ HP.classes [ H.ClassName "btn", H.ClassName "btn--primary" ]
              , HP.disabled state.isSaving
              , HE.onClick \_ -> Save
              ]
              [ HH.text $ if state.isSaving then "Saving..." else "Save Changes" ]
        ]
    ]

-- Helper components
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
            [ HP.type_ InputRange
            , HP.class_ (H.ClassName "slider")
            , HP.value (show config.value)
            , HP.min (show config.min)
            , HP.max (show config.max)
            , HP.step (show config.step)
            , HE.onValueChange (config.onChange <<< parseFloat)
            ]
        , HH.span [ HP.class_ (H.ClassName "slider-value") ] 
            [ HH.text (config.format config.value) ]
        ]
    ]

renderToggle :: forall m. ToggleConfig -> H.ComponentHTML Action () m
renderToggle config =
  HH.label
    [ HP.classes [ H.ClassName "settings-toggle", if config.disabled then H.ClassName "settings-toggle--disabled" else H.ClassName "" ] ]
    [ HH.input
        [ HP.type_ InputCheckbox
        , HP.checked config.checked
        , HP.disabled (fromMaybe false config.disabled)
        , HE.onChecked \_ -> config.onChange
        ]
    , HH.span [ HP.class_ (H.ClassName "toggle-label") ] 
        [ HH.text config.label ]
    ]
```

---

## CSS Styling

```css
.settings-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  overflow-y: auto;
  padding: var(--space-4);
}

.settings-panel__header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: var(--space-4);
  padding-bottom: var(--space-3);
  border-bottom: 1px solid var(--color-border-subtle);
}

.settings-panel__dirty-indicator {
  font-size: var(--font-size-sm);
  color: var(--color-warning);
}

.settings-section {
  margin-bottom: var(--space-6);
}

.settings-section__title {
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-secondary);
  text-transform: uppercase;
  letter-spacing: var(--letter-spacing-wider);
  margin-bottom: var(--space-3);
  padding-bottom: var(--space-2);
  border-bottom: 1px solid var(--color-border-subtle);
}

.settings-row {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: var(--space-3) 0;
}

.settings-row--slider {
  flex-direction: column;
  align-items: stretch;
  gap: var(--space-2);
}

.settings-label-group {
  display: flex;
  flex-direction: column;
  gap: var(--space-1);
}

.settings-label {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-text-primary);
}

.settings-description {
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
}

.slider-container {
  display: flex;
  align-items: center;
  gap: var(--space-3);
}

.slider {
  flex: 1;
  height: 4px;
  background: var(--color-border-default);
  border-radius: 2px;
  appearance: none;
}

.slider::-webkit-slider-thumb {
  appearance: none;
  width: 16px;
  height: 16px;
  background: var(--color-primary);
  border-radius: 50%;
  cursor: pointer;
}

.slider-value {
  min-width: 50px;
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-text-primary);
  text-align: right;
}

.settings-toggle {
  display: flex;
  align-items: center;
  gap: var(--space-3);
  padding: var(--space-2) 0;
  cursor: pointer;
}

.settings-toggle--disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.toggle-label {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-text-primary);
}

.radio-group {
  display: flex;
  gap: var(--space-4);
}

.settings-select {
  padding: var(--space-2) var(--space-3);
  background: var(--color-bg-base);
  border: 1px solid var(--color-border-default);
  border-radius: 6px;
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-text-primary);
}

.settings-panel__footer {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-top: auto;
  padding-top: var(--space-4);
  border-top: 1px solid var(--color-border-subtle);
}

.settings-version {
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
}

.settings-actions {
  display: flex;
  gap: var(--space-2);
}
```

---

## Persistence

### LocalStorage Keys

```typescript
const STORAGE_KEYS = {
  theme: 'sidepanel.settings.theme',
  alerts: 'sidepanel.settings.alerts',
  keyboard: 'sidepanel.settings.keyboard',
  features: 'sidepanel.settings.features',
  storage: 'sidepanel.settings.storage'
};
```

### Load/Save

```purescript
-- Load settings from localStorage
loadSettings :: Effect Settings
loadSettings = do
  stored <- getItem "sidepanel.settings"
  case stored >>= decodeJson of
    Just settings -> pure settings
    Nothing -> pure defaultSettings

-- Save settings to localStorage
saveSettings :: Settings -> Effect Unit
saveSettings settings = do
  setItem "sidepanel.settings" (encodeJson settings)
```

---

## Related Specifications

- `06-OPENCODE-CONFIG.md` - Config file settings
- `47-THEMING.md` - Theme implementation
- `48-KEYBOARD-NAVIGATION.md` - Keyboard settings

---

*"Good defaults make settings optional, not required."*
