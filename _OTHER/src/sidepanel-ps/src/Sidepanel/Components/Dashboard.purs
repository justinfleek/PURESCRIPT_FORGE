-- | Dashboard Component - Main Application Dashboard View
-- |
-- | **What:** Displays the main dashboard view showing balance, session, and proof
-- |         status widgets. This is the default landing view when the sidepanel opens.
-- | **Why:** Provides users with a unified view of their current system state, token
-- |         usage, active sessions, and Lean4 proof status. Centralizes key information
-- |         in a single view.
-- | **How:** Integrates with AppState to display three key widgets:
-- |         - Balance widget: Shows Venice Diem balance and token consumption
-- |         - Session widget: Shows current active session details
-- |         - Proof widget: Shows Lean4 LSP connection and goal status
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.AppState`: Provides application state
-- | - `Sidepanel.State.Balance`: Provides BalanceState type
-- |
-- | **Mathematical Foundation:**
-- | - **State Invariant:** Component's State is always equal to the AppState passed as
-- |   Input. This ensures the dashboard always reflects the current application state.
-- | - **Rendering Invariant:** All three widgets (balance, session, proof) are always
-- |   rendered, even if their data is empty (showing "No data" messages).
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Dashboard as Dashboard
-- |
-- | -- In parent component:
-- | HH.slot _dashboard unit Dashboard.component
-- |   { state: appState }
-- |   (const HandleAppAction)
-- |
-- | -- To update dashboard state:
-- | H.query _dashboard unit $ H.tell $ Dashboard.UpdateState newAppState
-- | ```
-- |
-- | Based on spec 50-DASHBOARD-LAYOUT.md
module Sidepanel.Components.Dashboard where

import Prelude
import Data.Array as Array
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Sidepanel.State.AppState (AppState, SessionState, ProofState)
import Sidepanel.State.Balance (BalanceState, FlkBalance)
import Sidepanel.Utils.Currency (formatDiem, formatFLK, formatUSD)

-- | Component input - Dashboard component input props
-- |
-- | **Purpose:** Receives the current application state to display in the dashboard.
-- | **Fields:**
-- | - `state`: Current application state
type Input = 
  { state :: AppState
  }

-- | Component output - Dashboard component output events
-- |
-- | **Purpose:** Currently unused - dashboard is a display-only component.
-- | **Future:** May emit events for widget interactions.
data Output = NoOp

-- | Component state - Dashboard internal state
-- |
-- | **Purpose:** Stores the application state for rendering.
-- | **Invariant:** State is always equal to the Input.state (no local state mutations).
-- | **Note:** This component is stateless - state comes entirely from props.
type State = AppState

-- | Component query - Dashboard component queries
-- |
-- | **Purpose:** Allows parent components to update the dashboard state.
-- | **Queries:**
-- | - `UpdateState newState`: Updates the dashboard to display newState
data Query a = UpdateState AppState a

-- | Dashboard component - Main dashboard component factory
-- |
-- | **Purpose:** Creates the dashboard component instance.
-- | **Returns:** A Halogen component that renders the dashboard view
-- | **Side Effects:** None (pure component creation)
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState: \input -> input.state
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleQuery = handleQuery
      }
  }

-- | Render function - Creates the dashboard HTML
-- |
-- | **Purpose:** Renders the dashboard view with three widgets: balance, session, and proof.
-- | **Parameters:**
-- | - `state`: The current application state to display
-- | **Returns:** Halogen HTML representing the dashboard
-- | **Side Effects:** None (pure rendering)
-- |
-- | **Rendering Structure:**
-- | - Outer container with "dashboard" class
-- | - Header with title
-- | - Content area containing three widgets
render :: forall m. State -> H.ComponentHTML () () m
render state =
  HH.div
    [ HP.classes [ H.ClassName "dashboard" ] ]
    [ HH.h1_ [ HH.text "OpenCode Sidepanel Dashboard" ]
    , HH.div
        [ HP.classes [ H.ClassName "dashboard-content" ] ]
        [ renderBalance state.balance
        , renderSession state.session
        , renderProof state.proof
        ]
    ]

renderBalance :: forall m. BalanceState -> H.ComponentHTML Action () m
renderBalance balance =
  HH.div
    [ HP.classes [ H.ClassName "balance-widget" ] ]
    [ HH.h2_ [ HH.text "Token Balance" ]
    , -- Show FLK balance if present (FLK takes priority)
      case balance.flk of
        Just flk ->
          HH.div_
            [ HH.p_ [ HH.text $ "FLK: " <> formatFLK flk.flk ]
            , HH.p_ [ HH.text $ "Effective: " <> formatFLK flk.effective ]
            , HH.p_ [ HH.text $ "Today Used: " <> formatFLK flk.todayUsed ]
            ]
        Nothing ->
          -- Show Venice balance if no FLK
          case balance.venice of
            Just venice ->
              HH.div_
                [ HH.p_ [ HH.text $ "Venice Diem: " <> formatDiem venice.diem ]
                , HH.p_ [ HH.text $ "USD: " <> formatUSD venice.usd ]
                , HH.p_ [ HH.text $ "Effective: " <> formatUSD venice.effective ]
                ]
            Nothing -> HH.p_ [ HH.text "No balance data" ]
    , HH.p_ [ HH.text $ "Total Tokens: " <> show balance.totalTokens.totalTokens ]
    , HH.p_ [ HH.text $ "Total Cost: " <> formatUSD balance.totalCost ]
    ]

-- | Render session widget - Display current session information
-- |
-- | **Purpose:** Displays the current active session information, including model,
-- |             tokens, and cost.
-- | **Parameters:**
-- | - `session`: Optional session state (Nothing if no active session)
-- | **Returns:** Halogen HTML for the session widget
-- | **Side Effects:** None (pure rendering)
-- |
-- | **Displays:**
-- | - Model name
-- | - Total tokens used in session
-- | - Session cost
renderSession :: forall m. Maybe Sidepanel.State.AppState.SessionState -> H.ComponentHTML Action () m
renderSession = case _ of
  Nothing -> HH.p_ [ HH.text "No active session" ]
  Just session ->
    HH.div
      [ HP.classes [ H.ClassName "session-widget" ] ]
      [ HH.h2_ [ HH.text "Current Session" ]
      , HH.p_ [ HH.text $ "Model: " <> session.model ]
      , HH.p_ [ HH.text $ "Tokens: " <> show session.totalTokens ]
      , HH.p_ [ HH.text $ "Cost: $" <> show session.cost ]
      ]

renderProof :: forall m. Sidepanel.State.AppState.ProofState -> H.ComponentHTML Action () m
renderProof proof =
  HH.div
    [ HP.classes [ H.ClassName "proof-widget" ] ]
    [ HH.h2_ [ HH.text "Lean4 Proof Status" ]
    , HH.p_ [ HH.text $ "Connected: " <> show proof.connected ]
    , HH.p_ [ HH.text $ "Goals: " <> show (Array.length proof.goals) ]
    ]

-- | Handle component queries - Process queries from parent components
-- |
-- | **Purpose:** Processes queries from parent components, currently only handles state updates.
-- | **Parameters:**
-- | - `query`: The query to process (currently only UpdateState)
-- | **Returns:** Maybe a continuation value
-- | **Side Effects:** Updates component state via H.put
handleQuery :: forall m a. Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  UpdateState newState k -> do
    H.put newState
    pure (Just k)
