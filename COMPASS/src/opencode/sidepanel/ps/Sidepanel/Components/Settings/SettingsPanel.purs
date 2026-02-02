-- | Settings Panel Component - Application Settings Management
-- |
-- | **What:** Provides a comprehensive settings interface for configuring alerts, appearance,
-- |         keyboard shortcuts, features, and storage.
-- | **Why:** Enables users to customize their sidepanel experience, configure alert thresholds,
-- |         choose themes, enable/disable features, and manage data retention.
-- | **How:** Renders settings sections with sliders, toggles, radio buttons, and dropdowns.
-- |         Tracks dirty state and provides save/reset functionality.
-- |
-- | Coeffect Equation:
-- |   SettingsPanel : Input -> Component q Input Output m
-- |   with persistence: Settings -o (LocalStorage * Bridge) -o Notification
-- |
-- | Module Structure:
-- |   SettingsPanel.Types   - Type definitions
-- |   SettingsPanel.Render  - Rendering functions
-- |   SettingsPanel.Handler - Action handling
-- |
-- | Based on spec 55-SETTINGS-PANEL.md
module Sidepanel.Components.Settings.SettingsPanel
  ( -- * Component
    component
    -- * Re-exports from Types
  , module Sidepanel.Components.Settings.SettingsPanel.Types
  ) where

import Prelude
import Halogen as H
import Effect.Aff.Class (class MonadAff)
import Data.Maybe (Maybe(..))

-- Re-export types
import Sidepanel.Components.Settings.SettingsPanel.Types
  ( State
  , Action(..)
  , Output(..)
  , Input
  , SliderConfig
  , ToggleConfig
  , initialState
  , settingsToSaveRequest
  , parseInt
  , parseFloat
  )

-- Internal imports
import Sidepanel.Components.Settings.SettingsPanel.Render (render)
import Sidepanel.Components.Settings.SettingsPanel.Handler (handleAction)

--------------------------------------------------------------------------------
-- | Component
--------------------------------------------------------------------------------

-- | Settings panel component
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
