-- | Sidebar Navigation Component - Main Navigation Sidebar
-- |
-- | **What:** Provides the main navigation sidebar with route selection, collapse/expand
-- |         functionality, connection status, and version display.
-- | **Why:** Enables users to navigate between different panels (Dashboard, Session,
-- |         Proof, Timeline, Settings) and provides visual feedback about connection
-- |         status and application version.
-- | **How:** Renders navigation items based on route, handles click events to emit
-- |         RouteSelected output, persists collapsed state to localStorage, and displays
-- |         connection status and version information.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Router`: Route definitions and printing
-- | - `Sidepanel.FFI.LocalStorage`: Persistence of collapsed state
-- |
-- | **Mathematical Foundation:**
-- | - **Route Matching:** `isRouteActive` determines if a route matches the current
-- |   route, handling parameterized routes (e.g., Session _) correctly.
-- | - **State Persistence:** Collapsed state is persisted to localStorage and restored
-- |   on initialization.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Sidebar as Sidebar
-- |
-- | -- In parent component:
-- | HH.slot _sidebar unit Sidebar.component currentRoute
-- |   (case _ of
-- |     Sidebar.RouteSelected route -> HandleRouteChange route)
-- | ```
-- |
-- | Based on spec 49-SIDEBAR-NAVIGATION.md
module Sidepanel.Components.Sidebar where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..), fromMaybe)
import Sidepanel.Router (Route(..), printRoute)
import Sidepanel.FFI.LocalStorage as LocalStorage

-- | Navigation item definition - Navigation menu item
-- |
-- | **Purpose:** Represents a single navigation item in the sidebar.
-- | **Fields:**
-- | - `route`: Route to navigate to when clicked
-- | - `icon`: Icon emoji or character
-- | - `label`: Display label
-- | - `shortcut`: Keyboard shortcut (displayed when not collapsed)
type NavItem =
  { route :: Route
  , icon :: String
  , label :: String
  , shortcut :: String
  }

-- | Component state
type State =
  { currentRoute :: Route
  , isCollapsed :: Boolean
  , isConnected :: Boolean
  , version :: String
  }


-- | Output to parent
data Output = RouteSelected Route

-- | Navigation items
navItems :: Array NavItem
navItems =
  [ { route: Dashboard, icon: "📊", label: "Dashboard", shortcut: "1" }
  , { route: Session Nothing, icon: "💬", label: "Session", shortcut: "2" }
  , { route: Proof, icon: "🔬", label: "Proofs", shortcut: "3" }
  , { route: Timeline, icon: "⏱", label: "Timeline", shortcut: "4" }
  ]

settingsItem :: NavItem
settingsItem = { route: Settings, icon: "⚙", label: "Settings", shortcut: "5" }

-- | Component input
type Input = Route

-- | Component
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< SetRoute
      , initialize = Just Initialize
      }
  }

initialState :: Input -> State
initialState route =
  { currentRoute: route
  , isCollapsed: false  -- Will be loaded from localStorage in Initialize
  , isConnected: true
  , version: "0.1.0"
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.nav
    [ HP.classes $ sidebarClasses state.isCollapsed
    , HP.attr (H.AttrName "role") "navigation"
    , HP.attr (H.AttrName "aria-label") "Main navigation"
    ]
    [ renderHeader state
    , HH.div
        [ HP.class_ (H.ClassName "sidebar__nav") ]
        (map (renderNavItem state) navItems)
    , HH.div [ HP.class_ (H.ClassName "sidebar__separator") ] []
    , HH.div
        [ HP.class_ (H.ClassName "sidebar__settings") ]
        [ renderNavItem state settingsItem ]
    , renderFooter state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.div
    [ HP.class_ (H.ClassName "sidebar__header") ]
    [ HH.div
        [ HP.class_ (H.ClassName "sidebar__logo")
        , HE.onClick \_ -> Navigate Dashboard
        ]
        [ HH.span [ HP.class_ (H.ClassName "logo-icon") ] [ HH.text "◉" ]
        , if not state.isCollapsed then
            HH.span [ HP.class_ (H.ClassName "logo-text") ] [ HH.text "SIDEPANEL" ]
          else
            HH.text ""
        ]
    , HH.button
        [ HP.class_ (H.ClassName "sidebar__toggle")
        , HP.attr (H.AttrName "aria-label") $
            if state.isCollapsed then "Expand sidebar" else "Collapse sidebar"
        , HE.onClick \_ -> ToggleCollapse
        ]
        [ HH.text $ if state.isCollapsed then "▶" else "◀" ]
    ]

renderNavItem :: forall m. State -> NavItem -> H.ComponentHTML Action () m
renderNavItem state item =
  let isActive = isRouteActive state.currentRoute item.route
  in
    HH.a
      [ HP.classes $ navItemClasses isActive
      , HP.href $ printRoute item.route
      , HP.attr (H.AttrName "role") "link"
      , HP.attr (H.AttrName "aria-current") $ if isActive then "page" else ""
      , HE.onClick \_ -> Navigate item.route
      ]
      [ HH.span [ HP.class_ (H.ClassName "nav-item__icon") ] [ HH.text item.icon ]
      , if not state.isCollapsed then
          HH.span [ HP.class_ (H.ClassName "nav-item__label") ] [ HH.text item.label ]
        else
          HH.text ""
      , if not state.isCollapsed then
          HH.span [ HP.class_ (H.ClassName "nav-item__shortcut") ] [ HH.text item.shortcut ]
        else
          HH.text ""
      ]

renderFooter :: forall m. State -> H.ComponentHTML Action () m
renderFooter state =
  HH.div
    [ HP.class_ (H.ClassName "sidebar__footer") ]
    [ HH.div
        [ HP.classes $ connectionClasses state.isConnected ]
        [ HH.span [ HP.class_ (H.ClassName "connection-dot") ] []
        , if not state.isCollapsed then
            HH.text $ if state.isConnected then "Connected" else "Disconnected"
          else
            HH.text ""
        ]
    , if not state.isCollapsed then
        HH.div
          [ HP.class_ (H.ClassName "sidebar__version") ]
          [ HH.text $ "v" <> state.version ]
      else
        HH.text ""
    ]

isRouteActive :: Route -> Route -> Boolean
isRouteActive current target = case current, target of
  Session _, Session _ -> true
  Dashboard, Dashboard -> true
  Proof, Proof -> true
  Timeline, Timeline -> true
  Settings, Settings -> true
  _, _ -> false

sidebarClasses :: Boolean -> Array H.ClassName
sidebarClasses isCollapsed =
  [ H.ClassName "sidebar" ] <>
  if isCollapsed then [ H.ClassName "sidebar--collapsed" ] else []

navItemClasses :: Boolean -> Array H.ClassName
navItemClasses isActive =
  [ H.ClassName "nav-item" ] <>
  if isActive then [ H.ClassName "nav-item--active" ] else []

connectionClasses :: Boolean -> Array H.ClassName
connectionClasses isConnected =
  [ H.ClassName "connection-status" ] <>
  if isConnected
    then [ H.ClassName "connection-status--connected" ]
    else [ H.ClassName "connection-status--disconnected" ]

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Load collapsed state from localStorage
    collapsed <- liftEffect $ LocalStorage.getItem "sidebar.collapsed"
    let isCollapsed = fromMaybe false $ collapsed >>= \s -> if s == "true" then Just true else Just false
    H.modify_ _ { isCollapsed = isCollapsed }

  Navigate route -> do
    H.modify_ _ { currentRoute = route }
    H.raise (RouteSelected route)

  ToggleCollapse -> do
    state <- H.get
    let newCollapsed = not state.isCollapsed
    H.modify_ _ { isCollapsed = newCollapsed }
    -- Persist preference to localStorage
    liftEffect $ LocalStorage.setItem "sidebar.collapsed" (if newCollapsed then "true" else "false")

  SetRoute route ->
    H.modify_ _ { currentRoute = route }

