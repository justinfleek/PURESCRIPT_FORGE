# 49-SIDEBAR-NAVIGATION: Navigation Sidebar Component

## Overview

The Sidebar provides navigation between major views (Dashboard, Session, Proofs, Timeline, Settings) with keyboard shortcuts and collapsible state.

---

## Visual Design

### Expanded State (Default)

```
┌─────────────────┐
│  ◉ SIDEPANEL    │
├─────────────────┤
│                 │
│  📊 Dashboard   │  ← Active (highlighted)
│  💬 Session     │
│  🔬 Proofs      │
│  ⏱  Timeline    │
│                 │
│  ─────────────  │
│                 │
│  ⚙ Settings     │
│                 │
├─────────────────┤
│  ◉ Connected    │
│  v0.1.0         │
└─────────────────┘
```

### Collapsed State

```
┌───┐
│ ◉ │
├───┤
│ 📊│  ← Active
│ 💬│
│ 🔬│
│ ⏱ │
├───┤
│ ⚙ │
├───┤
│ ◉ │
└───┘
```

---

## Navigation Items

| Key | Icon | Label | Route | Description |
|-----|------|-------|-------|-------------|
| 1 | 📊 | Dashboard | `/` | Balance, charts, session summary |
| 2 | 💬 | Session | `/session` | Message history, export |
| 3 | 🔬 | Proofs | `/proofs` | Lean4 proof state |
| 4 | ⏱ | Timeline | `/timeline` | Time-travel debugging |
| 5 | ⚙ | Settings | `/settings` | Configuration |

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.Sidebar where

import Prelude
import Data.Maybe (Maybe)
import Sidepanel.Router (Route(..))

-- Navigation item definition
type NavItem =
  { route :: Route
  , icon :: String
  , label :: String
  , shortcut :: String
  }

-- Component state
type State =
  { currentRoute :: Route
  , isCollapsed :: Boolean
  , isConnected :: Boolean
  , version :: String
  }

-- Actions
data Action
  = Navigate Route
  | ToggleCollapse
  | SetRoute Route

-- Output to parent
data Output = RouteSelected Route

-- Navigation items
navItems :: Array NavItem
navItems =
  [ { route: Dashboard, icon: "📊", label: "Dashboard", shortcut: "1" }
  , { route: Session,   icon: "💬", label: "Session",   shortcut: "2" }
  , { route: Proofs,    icon: "🔬", label: "Proofs",    shortcut: "3" }
  , { route: Timeline,  icon: "⏱",  label: "Timeline",  shortcut: "4" }
  ]

settingsItem :: NavItem
settingsItem = { route: Settings, icon: "⚙", label: "Settings", shortcut: "5" }
```

### Component

```purescript
component :: forall q m. MonadAff m => H.Component q Route Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< SetRoute
      }
  }

initialState :: Route -> State
initialState route =
  { currentRoute: route
  , isCollapsed: false
  , isConnected: true  -- Updated via WebSocket
  , version: "0.1.0"
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.nav
    [ HP.classes $ sidebarClasses state.isCollapsed
    , HP.attr (H.AttrName "role") "navigation"
    , HP.attr (H.AttrName "aria-label") "Main navigation"
    ]
    [ -- Header with logo/collapse toggle
      renderHeader state
    
    -- Main navigation items
    , HH.div
        [ HP.class_ (H.ClassName "sidebar__nav") ]
        (map (renderNavItem state) navItems)
    
    -- Separator
    , HH.div [ HP.class_ (H.ClassName "sidebar__separator") ] []
    
    -- Settings (separate from main nav)
    , HH.div
        [ HP.class_ (H.ClassName "sidebar__settings") ]
        [ renderNavItem state settingsItem ]
    
    -- Footer with connection status
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
        , unless state.isCollapsed $
            HH.span [ HP.class_ (H.ClassName "logo-text") ] [ HH.text "SIDEPANEL" ]
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
  let isActive = state.currentRoute == item.route
  in
    HH.a
      [ HP.classes $ navItemClasses isActive
      , HP.href $ routeToPath item.route
      , HP.attr (H.AttrName "role") "link"
      , HP.attr (H.AttrName "aria-current") $ if isActive then "page" else ""
      , HE.onClick \e -> do
          H.liftEffect $ preventDefault e
          Navigate item.route
      ]
      [ HH.span [ HP.class_ (H.ClassName "nav-item__icon") ] [ HH.text item.icon ]
      , unless state.isCollapsed $
          HH.span [ HP.class_ (H.ClassName "nav-item__label") ] [ HH.text item.label ]
      , unless state.isCollapsed $
          HH.span [ HP.class_ (H.ClassName "nav-item__shortcut") ] [ HH.text item.shortcut ]
      ]

renderFooter :: forall m. State -> H.ComponentHTML Action () m
renderFooter state =
  HH.div
    [ HP.class_ (H.ClassName "sidebar__footer") ]
    [ HH.div
        [ HP.classes $ connectionClasses state.isConnected ]
        [ HH.span [ HP.class_ (H.ClassName "connection-dot") ] []
        , unless state.isCollapsed $
            HH.text $ if state.isConnected then "Connected" else "Disconnected"
        ]
    , unless state.isCollapsed $
        HH.div
          [ HP.class_ (H.ClassName "sidebar__version") ]
          [ HH.text $ "v" <> state.version ]
    ]

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
```

### Actions

```purescript
handleAction :: forall m. MonadAff m 
             => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Navigate route -> do
    H.modify_ _ { currentRoute = route }
    H.raise (RouteSelected route)
  
  ToggleCollapse -> do
    H.modify_ \s -> s { isCollapsed = not s.isCollapsed }
    -- Persist preference
    isCollapsed <- H.gets _.isCollapsed
    H.liftEffect $ savePreference "sidebarCollapsed" (show isCollapsed)
  
  SetRoute route ->
    H.modify_ _ { currentRoute = route }
```

---

## CSS Styling

```css
.sidebar {
  display: flex;
  flex-direction: column;
  width: 200px;
  min-width: 200px;
  height: 100vh;
  background: var(--color-bg-surface);
  border-right: 1px solid var(--color-border-subtle);
  transition: width var(--transition-base), min-width var(--transition-base);
}

.sidebar--collapsed {
  width: 56px;
  min-width: 56px;
}

.sidebar__header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: var(--space-3);
  border-bottom: 1px solid var(--color-border-subtle);
}

.sidebar__logo {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  cursor: pointer;
}

.logo-icon {
  font-size: 20px;
  color: var(--color-primary);
}

.logo-text {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  font-weight: var(--font-weight-bold);
  color: var(--color-text-primary);
  letter-spacing: var(--letter-spacing-wider);
}

.sidebar__toggle {
  padding: var(--space-1);
  background: transparent;
  border: none;
  color: var(--color-text-tertiary);
  cursor: pointer;
  font-size: var(--font-size-xs);
  transition: color var(--transition-fast);
}

.sidebar__toggle:hover {
  color: var(--color-text-primary);
}

.sidebar__nav {
  flex: 1;
  padding: var(--space-2) 0;
}

.nav-item {
  display: flex;
  align-items: center;
  gap: var(--space-3);
  padding: var(--space-2) var(--space-3);
  color: var(--color-text-secondary);
  text-decoration: none;
  transition: all var(--transition-fast);
  cursor: pointer;
}

.nav-item:hover {
  color: var(--color-text-primary);
  background: var(--color-bg-hover);
}

.nav-item--active {
  color: var(--color-primary);
  background: var(--color-primary-dim);
  border-right: 2px solid var(--color-primary);
}

.nav-item__icon {
  font-size: 18px;
  width: 24px;
  text-align: center;
}

.nav-item__label {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  flex: 1;
}

.nav-item__shortcut {
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
  background: var(--color-bg-base);
  padding: 2px 6px;
  border-radius: 4px;
}

.sidebar__separator {
  height: 1px;
  background: var(--color-border-subtle);
  margin: var(--space-2) var(--space-3);
}

.sidebar__settings {
  padding: var(--space-2) 0;
}

.sidebar__footer {
  padding: var(--space-3);
  border-top: 1px solid var(--color-border-subtle);
}

.connection-status {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
}

.connection-dot {
  width: 8px;
  height: 8px;
  border-radius: 50%;
}

.connection-status--connected .connection-dot {
  background: var(--color-success);
}

.connection-status--disconnected .connection-dot {
  background: var(--color-error);
}

.sidebar__version {
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
  margin-top: var(--space-1);
}

/* Collapsed state adjustments */
.sidebar--collapsed .nav-item {
  justify-content: center;
  padding: var(--space-2);
}

.sidebar--collapsed .nav-item__icon {
  margin: 0;
}

.sidebar--collapsed .sidebar__footer {
  justify-content: center;
}

/* Mobile: bottom navigation */
@media (max-width: 768px) {
  .sidebar {
    position: fixed;
    bottom: 0;
    left: 0;
    right: 0;
    width: 100%;
    height: 56px;
    flex-direction: row;
    border-right: none;
    border-top: 1px solid var(--color-border-subtle);
  }
  
  .sidebar__header,
  .sidebar__separator,
  .sidebar__footer {
    display: none;
  }
  
  .sidebar__nav {
    display: flex;
    justify-content: space-around;
    width: 100%;
    padding: 0;
  }
  
  .nav-item {
    flex-direction: column;
    padding: var(--space-2);
    gap: var(--space-1);
  }
  
  .nav-item--active {
    border-right: none;
    border-top: 2px solid var(--color-primary);
  }
  
  .nav-item__label {
    font-size: 10px;
  }
  
  .nav-item__shortcut {
    display: none;
  }
}
```

---

## Keyboard Navigation

The sidebar responds to number keys for quick navigation:

```purescript
-- In global keyboard handler
handleKeyDown event
  | key == "1" = Navigate Dashboard
  | key == "2" = Navigate Session
  | key == "3" = Navigate Proofs
  | key == "4" = Navigate Timeline
  | key == "5" = Navigate Settings
  | key == "[" = ToggleCollapse  -- Bracket to collapse
```

---

## Related Specifications

- `48-KEYBOARD-NAVIGATION.md` - Keyboard shortcuts
- `50-DASHBOARD-LAYOUT.md` - Main content area
- `40-PURESCRIPT-ARCHITECTURE.md` - Component patterns

---

*"Navigation should be invisible until you need it."*
