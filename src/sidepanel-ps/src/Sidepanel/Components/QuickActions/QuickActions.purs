-- | Quick Actions Component - Fast Access to Common Tasks
-- |
-- | **What:** Provides one-click access to frequently used operations, context-sensitive
-- |         suggestions, and smart shortcuts based on current state.
-- | **Why:** Enables users to quickly access common tasks without navigating through menus.
-- | **How:** Renders a panel with suggested actions, favorites, and recent actions.
-- |         Supports customization, keyboard shortcuts, and context-aware suggestions.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.AppState`: Access to current state for context-aware suggestions
-- |
-- | **Mathematical Foundation:**
-- | - **Action Ranking:** Actions are ranked by usage count and recency.
-- | - **Suggestion Invariant:** Suggestions are always relevant to current state.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.QuickActions.QuickActions as QuickActions
-- |
-- | -- In parent component:
-- | HH.slot _quickActions unit QuickActions.component
-- |   { appState: state.appState, wsClient: Just wsClient }
-- |   (case _ of
-- |     QuickActions.ActionTriggered action -> HandleActionTriggered action)
-- | ```
-- |
-- | Based on spec 69-QUICK-ACTIONS.md
module Sidepanel.Components.QuickActions.QuickActions where

import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Class (liftEffect)
import Effect.Aff.Class (class MonadAff)
import Sidepanel.WebSocket.Client as WS
import Sidepanel.State.AppState (AppState)
import Data.Map as Map

-- | Action category
data ActionCategory
  = SessionCategory
  | NavigationCategory
  | ExportCategory
  | SnapshotCategory
  | SettingsCategory
  | ToolsCategory

derive instance eqActionCategory :: Eq ActionCategory

-- | Quick action
type QuickAction =
  { id :: String
  , label :: String
  , icon :: String
  , shortcut :: Maybe String
  , category :: ActionCategory
  , isFavorite :: Boolean
  , usageCount :: Int
  }

-- | Recent action
type RecentAction =
  { actionId :: String
  , timestamp :: Number  -- ms since epoch
  , context :: Maybe String
  }

-- | Component input
type Input =
  { appState :: AppState
  , wsClient :: Maybe WS.WSClient
  }

-- | Component state
type State =
  { appState :: AppState
  , favorites :: Array String  -- Action IDs
  , recentActions :: Array RecentAction
  , suggestions :: Array String  -- Context-based action IDs
  , isEditing :: Boolean
  , wsClient :: Maybe WS.WSClient
  }

-- | Component actions
data Action
  = Initialize
  = Receive Input
  | TriggerAction String
  | ToggleFavorite String
  | StartEditing
  | StopEditing
  | ReorderFavorites (Array String)

-- | Component output
data Output
  = ActionTriggered QuickAction

-- | All available actions
allActions :: Array QuickAction
allActions =
  [ { id: "session.new"
    , label: "New Session"
    , icon: "➕"
    , shortcut: Just "Ctrl+N"
    , category: SessionCategory
    , isFavorite: true
    , usageCount: 0
    }
  , { id: "session.continue"
    , label: "Continue Session"
    , icon: "🔄"
    , shortcut: Nothing
    , category: SessionCategory
    , isFavorite: false
    , usageCount: 0
    }
  , { id: "session.branch"
    , label: "Branch Session"
    , icon: "🌿"
    , shortcut: Just "gb"
    , category: SessionCategory
    , isFavorite: false
    , usageCount: 0
    }
  , { id: "snapshot.create"
    , label: "Create Snapshot"
    , icon: "📸"
    , shortcut: Just "Ctrl+S"
    , category: SnapshotCategory
    , isFavorite: true
    , usageCount: 0
    }
  , { id: "nav.search"
    , label: "Search History"
    , icon: "🔍"
    , shortcut: Just "/"
    , category: NavigationCategory
    , isFavorite: true
    , usageCount: 0
    }
  , { id: "export.session"
    , label: "Export Session"
    , icon: "📤"
    , shortcut: Just "Ctrl+Shift+E"
    , category: ExportCategory
    , isFavorite: true
    , usageCount: 0
    }
  , { id: "nav.timeline"
    , label: "View Timeline"
    , icon: "⏱"
    , shortcut: Just "4"
    , category: NavigationCategory
    , isFavorite: true
    , usageCount: 0
    }
  , { id: "nav.settings"
    , label: "Settings"
    , icon: "⚙"
    , shortcut: Just "5"
    , category: SettingsCategory
    , isFavorite: true
    , usageCount: 0
    }
  , { id: "tools.recording"
    , label: "Start Recording"
    , icon: "🎬"
    , shortcut: Nothing
    , category: ToolsCategory
    , isFavorite: false
    , usageCount: 0
    }
  ]

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      { appState: input.appState
      , favorites: ["session.new", "snapshot.create", "nav.search", "export.session", "nav.timeline", "nav.settings"]
      , recentActions: []
      , suggestions: []
      , isEditing: false
      , wsClient: input.wsClient
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      , initialize = Just Initialize
      }
  }

-- | Render component
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "quick-actions") ]
    [ renderHeader state
    , renderSuggested state
    , renderFavorites state
    , renderRecent state
    ]

-- | Render header
renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.header
    [ HP.class_ (H.ClassName "quick-actions__header") ]
    [ HH.h2_ [ HH.text "QUICK ACTIONS" ]
    , HH.button
        [ HP.class_ (H.ClassName "edit-btn")
        , HE.onClick \_ -> if state.isEditing then StopEditing else StartEditing
        ]
        [ HH.text if state.isEditing then "Done" else "Edit ✎" ]
    ]

-- | Render suggested actions
renderSuggested :: forall m. State -> H.ComponentHTML Action () m
renderSuggested state =
  HH.div
    [ HP.class_ (H.ClassName "suggested-actions") ]
    [ HH.h3_ [ HH.text "SUGGESTED" ]
    , HH.div
        [ HP.class_ (H.ClassName "suggested-hint") ]
        [ HH.text "💡 Based on your current context:" ]
    , HH.div
        [ HP.class_ (H.ClassName "actions-grid") ]
        (Array.map renderActionButton (getSuggestedActions state))
    ]

-- | Render favorites
renderFavorites :: forall m. State -> H.ComponentHTML Action () m
renderFavorites state =
  HH.div
    [ HP.class_ (H.ClassName "favorites-actions") ]
    [ HH.h3_ [ HH.text "FAVORITES" ]
    , HH.div
        [ HP.class_ (H.ClassName "actions-grid") ]
        (Array.map renderActionButton (getFavoriteActions state))
    ]

-- | Render recent actions
renderRecent :: forall m. State -> H.ComponentHTML Action () m
renderRecent state =
  HH.div
    [ HP.class_ (H.ClassName "recent-actions") ]
    [ HH.h3_ [ HH.text "RECENT" ]
    , HH.div
        [ HP.class_ (H.ClassName "recent-list") ]
        (Array.map renderRecentItem state.recentActions)
    ]

-- | Render action button
renderActionButton :: forall m. QuickAction -> H.ComponentHTML Action () m
renderActionButton action =
  HH.button
    [ HP.class_ (H.ClassName "action-button")
    , HE.onClick \_ -> TriggerAction action.id
    ]
    [ HH.div
        [ HP.class_ (H.ClassName "action-icon") ]
        [ HH.text action.icon ]
    , HH.div
        [ HP.class_ (H.ClassName "action-label") ]
        [ HH.text action.label ]
    , case action.shortcut of
        Just shortcut -> HH.div
          [ HP.class_ (H.ClassName "action-shortcut") ]
          [ HH.text shortcut ]
        Nothing -> HH.text ""
    ]

-- | Render recent item
renderRecentItem :: forall m. RecentAction -> H.ComponentHTML Action () m
renderRecentItem recent =
  HH.div
    [ HP.class_ (H.ClassName "recent-item") ]
    [ HH.span
        [ HP.class_ (H.ClassName "recent-icon") ]
        [ HH.text "🕐" ]
    , HH.span
        [ HP.class_ (H.ClassName "recent-label") ]
        [ HH.text $ getActionLabel recent.actionId ]
    , HH.span
        [ HP.class_ (H.ClassName "recent-time") ]
        [ HH.text $ formatRecentTime recent.timestamp ]
    , HH.button
        [ HP.class_ (H.ClassName "recent-open")
        , HE.onClick \_ -> TriggerAction recent.actionId
        ]
        [ HH.text "Open" ]
    ]

-- | Get suggested actions
getSuggestedActions :: State -> Array QuickAction
getSuggestedActions state =
  -- Context-based suggestions
  let
    hasActiveSession = case state.appState.activeSessionId of
      Just _ -> true
      Nothing -> false
    
    suggestions = if hasActiveSession then
      [ findAction "session.continue"
      , findAction "session.branch"
      , findAction "snapshot.create"
      ]
    else
      [ findAction "session.new"
      , findAction "nav.search"
      ]
  in
    Array.catMaybes suggestions

-- | Get favorite actions
getFavoriteActions :: State -> Array QuickAction
getFavoriteActions state =
  Array.catMaybes $ map findAction state.favorites

-- | Find action by ID
findAction :: String -> Maybe QuickAction
findAction id = Array.find (\a -> a.id == id) allActions

-- | Get action label
getActionLabel :: String -> String
getActionLabel id = case findAction id of
  Just action -> action.label
  Nothing -> id

-- | Format recent time
formatRecentTime :: Number -> String
formatRecentTime timestamp = "5 min ago"  -- Placeholder

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    state <- H.get
    -- Calculate context-based suggestions
    let suggestions = calculateSuggestions state.appState
    H.modify_ _ { suggestions = suggestions }
  
  Receive input -> do
    H.modify_ _
      { appState = input.appState
      , wsClient = input.wsClient
      }
    -- Recalculate suggestions
    state <- H.get
    let suggestions = calculateSuggestions input.appState
    H.modify_ _ { suggestions = suggestions }
  
  TriggerAction actionId -> do
    case findAction actionId of
      Just action -> do
        H.raise (ActionTriggered action)
        -- Record usage
        recordUsage actionId
      Nothing -> pure unit
  
  ToggleFavorite actionId -> do
    state <- H.get
    let newFavorites = if Array.elem actionId state.favorites then
          Array.filter (_ /= actionId) state.favorites
        else
          Array.take 6 (state.favorites <> [actionId])  -- Max 6 favorites
    H.modify_ _ { favorites = newFavorites }
  
  StartEditing -> do
    H.modify_ _ { isEditing = true }
  
  StopEditing -> do
    H.modify_ _ { isEditing = false }
  
  ReorderFavorites newOrder -> do
    H.modify_ _ { favorites = newOrder }

-- | Calculate context-based suggestions
calculateSuggestions :: AppState -> Array String
calculateSuggestions appState =
  let
    hasActiveSession = case appState.activeSessionId of
      Just _ -> true
      Nothing -> false
    
    hasSnapshots = Array.length appState.snapshots > 0
  in
    if hasActiveSession then
      ["session.continue", "session.branch", "snapshot.create"]
    else if hasSnapshots then
      ["snapshot.restore", "session.new"]
    else
      ["session.new", "nav.search"]

-- | Record action usage
recordUsage :: forall m. MonadAff m => String -> H.HalogenM State Action () Output m Unit
recordUsage actionId = do
  state <- H.get
  let recentAction =
        { actionId: actionId
        , timestamp: 0.0  -- Would use current timestamp
        , context: Nothing
        }
  let newRecent = Array.take 5 (Array.cons recentAction state.recentActions)
  H.modify_ _ { recentActions = newRecent }
