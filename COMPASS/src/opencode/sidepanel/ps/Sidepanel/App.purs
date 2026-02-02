-- | Main App Component - Root Application Component with Routing and State Management
-- |
-- | **What:** The root Halogen component that orchestrates the entire sidepanel application,
-- |         including routing, WebSocket connection, theme management, and all child components.
-- | **Why:** Provides the top-level application structure, manages global state transitions,
-- |         handles routing between panels, and coordinates communication between components.
-- | **How:** Uses Halogen component architecture with hash-based routing, WebSocket client,
-- |         state reducer pattern, and component slots for all child components.
-- |
-- | Coeffect Equation:
-- |   App : Unit -> Component q Unit Void m
-- |   with resources: WebSocket^1 * Theme^1 * Router^1 -o Application
-- |
-- | Module Structure:
-- |   App.Types   - Slots, State, Action definitions
-- |   App.Render  - All rendering functions
-- |   App.Handler - Action handling logic
-- |   App.Helpers - Utility functions
-- |
-- | Based on spec 50-DASHBOARD-LAYOUT.md
module Sidepanel.App
  ( -- * Component
    component
    -- * Re-exports from Types
  , module Sidepanel.App.Types
  ) where

import Prelude
import Halogen as H
import Effect.Aff.Class (class MonadAff)
import Data.Maybe (Maybe(..))
import Sidepanel.Router (Route(..))
import Sidepanel.State.AppState (initialState)

-- Re-export types
import Sidepanel.App.Types
  ( Slots
  , State
  , Action(..)
  , _sidebar
  , _dashboard
  , _session
  , _proof
  , _timeline
  , _settings
  , _balanceTracker
  , _tokenChart
  , _alertSystem
  , _keyboardNavigation
  , _commandPalette
  , _terminalEmbed
  , _fileContextView
  , _diffViewer
  , _helpOverlay
  )

-- Internal imports
import Sidepanel.App.Render (render)
import Sidepanel.App.Handler (handleAction)

--------------------------------------------------------------------------------
-- | Component
--------------------------------------------------------------------------------

-- | App component - Root Halogen component
-- |
-- | Creates the root application component that manages routing, state,
-- | WebSocket connection, and all child components.
component :: forall q m. MonadAff m => H.Component q Unit Void m
component = H.mkComponent
  { initialState: const
      { appState: initialState
      , currentRoute: Dashboard
      , wsClient: Nothing
      , helpOverlayVisible: false
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }
