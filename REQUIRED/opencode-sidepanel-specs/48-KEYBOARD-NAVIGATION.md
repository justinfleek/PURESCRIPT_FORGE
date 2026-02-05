# 48-KEYBOARD-NAVIGATION: Vim Bindings and Command Palette

## Overview

Keyboard-first navigation is essential for our target audience of terminal power users. The sidepanel provides comprehensive Vim-style navigation and a command palette for discoverability.

---

## Design Principles

1. **No mouse required** - Every action accessible via keyboard
2. **Familiar patterns** - Vim users feel at home
3. **Discoverable** - Command palette shows all available actions
4. **Non-conflicting** - Don't steal focus from terminal
5. **Configurable** - Users can customize bindings (Phase 2)

---

## Global Keybindings

### Navigation

| Key | Action | Context |
|-----|--------|---------|
| `j` | Move down / Next item | Lists, panels |
| `k` | Move up / Previous item | Lists, panels |
| `h` | Collapse / Go left | Trees, panels |
| `l` | Expand / Go right | Trees, panels |
| `gg` | Go to first item | Lists |
| `G` | Go to last item | Lists |
| `Ctrl+d` | Page down | Long lists |
| `Ctrl+u` | Page up | Long lists |

### Search

| Key | Action |
|-----|--------|
| `/` | Open search |
| `n` | Next search result |
| `N` | Previous search result |
| `Esc` | Close search |

### Panels

| Key | Action |
|-----|--------|
| `1` | Go to Dashboard |
| `2` | Go to Session |
| `3` | Go to Proofs |
| `4` | Go to Timeline |
| `5` | Go to Settings |
| `Tab` | Next panel |
| `Shift+Tab` | Previous panel |

### Actions

| Key | Action |
|-----|--------|
| `Ctrl+Shift+P` | Command palette |
| `r` | Refresh current view |
| `?` | Show keyboard help |
| `Esc` | Close modal / Cancel |
| `Enter` | Confirm / Select |
| `Space` | Toggle selection |

### Quick Actions

| Key | Action |
|-----|--------|
| `gb` | Go to balance view |
| `gc` | Go to countdown |
| `gs` | Go to session |
| `gp` | Go to proofs |
| `gt` | Go to timeline |

---

## Command Palette

### Opening

```
Ctrl+Shift+P  or  :  (Vim command mode)
```

### Interface

```
┌─────────────────────────────────────────────────────────────┐
│ >                                                           │
├─────────────────────────────────────────────────────────────┤
│ ▸ Dashboard                                           ⌘1    │
│   Session Details                                     ⌘2    │
│   Proof Status                                        ⌘3    │
│   Timeline                                            ⌘4    │
│   Settings                                            ⌘5    │
│ ──────────────────────────────────────────────────────────  │
│   Refresh Balance                                     r     │
│   Export Session                                      ⌘E    │
│   Create Snapshot                                     ⌘S    │
│   Toggle Theme                                              │
└─────────────────────────────────────────────────────────────┘
```

### Fuzzy Search

```
> sess          # Matches "Session Details", "Session Export"
> bal ref       # Matches "Refresh Balance"
> snap          # Matches "Create Snapshot"
```

### Command Categories

| Category | Commands |
|----------|----------|
| Navigation | Dashboard, Session, Proofs, Timeline, Settings |
| Balance | Refresh Balance, Set Alert Threshold |
| Session | Export Session, Clear Session, View History |
| Timeline | Create Snapshot, Restore Snapshot |
| Proofs | Check Proof, Suggest Tactic, Search Theorems |
| Settings | Toggle Theme, Configure Alerts, Reset Settings |

---

## Implementation

### PureScript Keyboard Hook

```purescript
module Sidepanel.Hooks.UseKeyboard where

import Prelude
import Data.Maybe (Maybe(..))
import Data.String (toLower)
import Effect (Effect)
import Web.UIEvent.KeyboardEvent (KeyboardEvent)
import Web.UIEvent.KeyboardEvent as KE

-- Key binding definition
data KeyBinding
  = SimpleKey String              -- "j", "k", "/", etc.
  | ModifierKey Modifier String   -- Ctrl+P, Shift+Tab
  | Sequence (Array String)       -- "gg", "gc"

data Modifier = Ctrl | Shift | Alt | Meta | CtrlShift

-- Match a keyboard event against a binding
matchBinding :: KeyBinding -> KeyboardEvent -> Boolean
matchBinding binding event = case binding of
  SimpleKey key -> 
    not (hasModifier event) && 
    toLower (KE.key event) == toLower key
    
  ModifierKey mod key ->
    hasModifier event &&
    matchModifier mod event &&
    toLower (KE.key event) == toLower key
    
  Sequence keys ->
    -- Handled by sequence tracker
    false

hasModifier :: KeyboardEvent -> Boolean
hasModifier e = KE.ctrlKey e || KE.shiftKey e || KE.altKey e || KE.metaKey e

matchModifier :: Modifier -> KeyboardEvent -> Boolean
matchModifier Ctrl e = KE.ctrlKey e && not (KE.shiftKey e)
matchModifier Shift e = KE.shiftKey e && not (KE.ctrlKey e)
matchModifier Alt e = KE.altKey e
matchModifier Meta e = KE.metaKey e
matchModifier CtrlShift e = KE.ctrlKey e && KE.shiftKey e
```

### Sequence Detection (for gg, gc, etc.)

```purescript
module Sidepanel.Utils.KeySequence where

import Prelude
import Effect.Ref (Ref, new, read, write)
import Effect.Timer (setTimeout, clearTimeout)

type SequenceState =
  { buffer :: Array String
  , timeout :: Maybe TimeoutId
  }

-- Track key sequences with timeout
createSequenceTracker 
  :: (Array String -> Effect Unit)  -- Handler when sequence completes
  -> Effect { push :: String -> Effect Unit, reset :: Effect Unit }
createSequenceTracker onSequence = do
  stateRef <- new { buffer: [], timeout: Nothing }
  
  let
    reset = do
      state <- read stateRef
      for_ state.timeout clearTimeout
      write { buffer: [], timeout: Nothing } stateRef
    
    push key = do
      state <- read stateRef
      for_ state.timeout clearTimeout
      
      let newBuffer = state.buffer <> [key]
      
      -- Check for known sequences
      case matchSequence newBuffer of
        Just action -> do
          onSequence newBuffer
          reset
        Nothing -> do
          -- Set timeout to reset buffer
          timeoutId <- setTimeout 500 reset
          write { buffer: newBuffer, timeout: Just timeoutId } stateRef
  
  pure { push, reset }

-- Check if buffer matches any known sequence
matchSequence :: Array String -> Maybe String
matchSequence buffer = case buffer of
  ["g", "g"] -> Just "goToTop"
  ["g", "b"] -> Just "goToBalance"
  ["g", "c"] -> Just "goToCountdown"
  ["g", "s"] -> Just "goToSession"
  ["g", "p"] -> Just "goToProofs"
  ["g", "t"] -> Just "goToTimeline"
  _ -> Nothing
```

### Global Keyboard Handler Component

```purescript
module Sidepanel.Components.KeyboardHandler where

import Prelude
import Halogen as H
import Web.UIEvent.KeyboardEvent (KeyboardEvent)
import Web.UIEvent.KeyboardEvent as KE
import Web.HTML (window)
import Web.HTML.Window (document)
import Web.HTML.HTMLDocument (toEventTarget)
import Web.Event.EventTarget (addEventListener, removeEventListener)

data Action
  = Initialize
  | HandleKeyDown KeyboardEvent
  | HandleKeyUp KeyboardEvent

type State = 
  { commandPaletteOpen :: Boolean
  , sequenceBuffer :: Array String
  }

component :: forall q i m. MonadAff m => H.Component q i Output m
component = H.mkComponent
  { initialState: const { commandPaletteOpen: false, sequenceBuffer: [] }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Add global keyboard listener
    doc <- H.liftEffect $ document =<< window
    let target = toEventTarget doc
    
    keydownListener <- H.liftEffect $ eventListener \e -> do
      for_ (KE.fromEvent e) \ke -> do
        -- Emit to component
        pure unit  -- Would need subscription setup
    
    H.liftEffect $ addEventListener keydown keydownListener false target
    
    -- Store cleanup function
    H.modify_ _ { cleanup = Just $ removeEventListener keydown keydownListener false target }

  HandleKeyDown event -> do
    state <- H.get
    
    -- Don't handle if input is focused
    when (not $ isInputFocused event) do
      case getAction event state of
        Just action -> do
          H.liftEffect $ KE.preventDefault event
          executeAction action
        Nothing ->
          pure unit

  HandleKeyUp _ -> pure unit

-- Determine action from key event
getAction :: KeyboardEvent -> State -> Maybe KeyboardAction
getAction event state
  -- Command palette
  | KE.ctrlKey event && KE.shiftKey event && KE.key event == "p" = 
      Just OpenCommandPalette
  
  -- Search
  | KE.key event == "/" && not (KE.ctrlKey event) = 
      Just OpenSearch
  
  -- Navigation
  | KE.key event == "j" = Just MoveDown
  | KE.key event == "k" = Just MoveUp
  | KE.key event == "h" = Just MoveLeft
  | KE.key event == "l" = Just MoveRight
  
  -- Page navigation
  | KE.key event == "1" = Just (GoToPanel Dashboard)
  | KE.key event == "2" = Just (GoToPanel Session)
  | KE.key event == "3" = Just (GoToPanel Proofs)
  | KE.key event == "4" = Just (GoToPanel Timeline)
  | KE.key event == "5" = Just (GoToPanel Settings)
  
  -- Actions
  | KE.key event == "r" = Just Refresh
  | KE.key event == "?" = Just ShowHelp
  | KE.key event == "Escape" = Just Cancel
  | KE.key event == "Enter" = Just Confirm
  
  | otherwise = Nothing

-- Check if an input element has focus
isInputFocused :: KeyboardEvent -> Boolean
isInputFocused event = 
  let target = KE.target event
  in case tagName target of
    "INPUT" -> true
    "TEXTAREA" -> true
    "SELECT" -> true
    _ -> false
```

---

## Command Palette Component

```purescript
module Sidepanel.Components.CommandPalette where

import Prelude
import Data.Array as Array
import Data.String (contains, Pattern(..), toLower)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE

type Command =
  { id :: String
  , label :: String
  , shortcut :: Maybe String
  , category :: String
  , action :: Effect Unit
  }

type State =
  { query :: String
  , commands :: Array Command
  , filteredCommands :: Array Command
  , selectedIndex :: Int
  }

data Action
  = UpdateQuery String
  | SelectCommand Int
  | ExecuteSelected
  | MoveSelection Int
  | Close

component :: forall q m. MonadAff m => H.Component q (Array Command) Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

initialState :: Array Command -> State
initialState commands =
  { query: ""
  , commands
  , filteredCommands: commands
  , selectedIndex: 0
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "command-palette-overlay")
    , HE.onClick \_ -> Close
    ]
    [ HH.div
        [ HP.class_ (H.ClassName "command-palette")
        , HE.onClick \e -> H.liftEffect (stopPropagation e)
        ]
        [ -- Search input
          HH.div
            [ HP.class_ (H.ClassName "command-palette__input-wrapper") ]
            [ HH.span 
                [ HP.class_ (H.ClassName "command-palette__prompt") ]
                [ HH.text ">" ]
            , HH.input
                [ HP.type_ InputText
                , HP.class_ (H.ClassName "command-palette__input")
                , HP.value state.query
                , HP.placeholder "Type a command..."
                , HP.autofocus true
                , HE.onValueInput UpdateQuery
                , HE.onKeyDown handleInputKeyDown
                ]
            ]
        
        -- Command list
        , HH.div
            [ HP.class_ (H.ClassName "command-palette__list") ]
            (Array.mapWithIndex renderCommand state.filteredCommands)
        ]
    ]

renderCommand :: forall m. Int -> Command -> H.ComponentHTML Action () m
renderCommand index cmd =
  HH.div
    [ HP.classes $ commandClasses index
    , HE.onClick \_ -> SelectCommand index
    , HE.onDoubleClick \_ -> ExecuteSelected
    ]
    [ HH.span 
        [ HP.class_ (H.ClassName "command-label") ]
        [ HH.text cmd.label ]
    , case cmd.shortcut of
        Just shortcut ->
          HH.span 
            [ HP.class_ (H.ClassName "command-shortcut") ]
            [ HH.text shortcut ]
        Nothing -> HH.text ""
    ]

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  UpdateQuery query -> do
    commands <- H.gets _.commands
    let filtered = filterCommands query commands
    H.modify_ _ 
      { query = query
      , filteredCommands = filtered
      , selectedIndex = 0
      }
  
  SelectCommand index ->
    H.modify_ _ { selectedIndex = index }
  
  ExecuteSelected -> do
    state <- H.get
    case Array.index state.filteredCommands state.selectedIndex of
      Just cmd -> do
        H.liftEffect cmd.action
        H.raise CommandExecuted
      Nothing -> pure unit
  
  MoveSelection delta -> do
    state <- H.get
    let 
      maxIndex = Array.length state.filteredCommands - 1
      newIndex = clamp 0 maxIndex (state.selectedIndex + delta)
    H.modify_ _ { selectedIndex = newIndex }
  
  Close ->
    H.raise PaletteClosed

-- Fuzzy filter commands
filterCommands :: String -> Array Command -> Array Command
filterCommands query commands
  | query == "" = commands
  | otherwise = 
      Array.filter (matchCommand (toLower query)) commands

matchCommand :: String -> Command -> Boolean
matchCommand query cmd =
  contains (Pattern query) (toLower cmd.label) ||
  contains (Pattern query) (toLower cmd.category)
```

---

## CSS Styling

```css
/* Command Palette */
.command-palette-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0, 0, 0, 0.5);
  display: flex;
  justify-content: center;
  padding-top: 20vh;
  z-index: 1000;
}

.command-palette {
  width: 500px;
  max-height: 400px;
  background: var(--surface-elevated);
  border: 1px solid var(--border-subtle);
  border-radius: 8px;
  box-shadow: 0 25px 50px -12px rgba(0, 0, 0, 0.5);
  overflow: hidden;
}

.command-palette__input-wrapper {
  display: flex;
  align-items: center;
  padding: 12px 16px;
  border-bottom: 1px solid var(--border-subtle);
}

.command-palette__prompt {
  color: var(--color-primary);
  font-family: var(--font-mono);
  font-size: 18px;
  margin-right: 8px;
}

.command-palette__input {
  flex: 1;
  background: transparent;
  border: none;
  outline: none;
  color: var(--text-primary);
  font-family: var(--font-mono);
  font-size: 16px;
}

.command-palette__list {
  max-height: 300px;
  overflow-y: auto;
}

.command-item {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 10px 16px;
  cursor: pointer;
}

.command-item:hover,
.command-item--selected {
  background: var(--surface-hover);
}

.command-item--selected {
  background: var(--color-primary-dim);
}

.command-label {
  color: var(--text-primary);
}

.command-shortcut {
  color: var(--text-tertiary);
  font-family: var(--font-mono);
  font-size: 12px;
  background: var(--surface-default);
  padding: 2px 6px;
  border-radius: 4px;
}

/* Keyboard Help Overlay */
.keyboard-help {
  display: grid;
  grid-template-columns: repeat(2, 1fr);
  gap: 24px;
  padding: 24px;
}

.keyboard-section h3 {
  font-size: 14px;
  color: var(--text-secondary);
  margin-bottom: 12px;
  text-transform: uppercase;
  letter-spacing: 0.05em;
}

.key-binding {
  display: flex;
  justify-content: space-between;
  padding: 6px 0;
}

.key {
  font-family: var(--font-mono);
  background: var(--surface-default);
  padding: 2px 8px;
  border-radius: 4px;
  font-size: 13px;
}
```

---

## Accessibility

Keyboard navigation supports screen readers:

```purescript
-- ARIA attributes for command palette
HH.div
  [ HP.attr (H.AttrName "role") "listbox"
  , HP.attr (H.AttrName "aria-label") "Command palette"
  , HP.attr (H.AttrName "aria-activedescendant") (selectedId state)
  ]
  [ ... ]

-- Each command item
HH.div
  [ HP.attr (H.AttrName "role") "option"
  , HP.attr (H.AttrName "aria-selected") (if selected then "true" else "false")
  , HP.id itemId
  ]
  [ ... ]
```

---

## Related Specifications

- `58-COMMAND-PALETTE.md` - Command palette details
- `40-PURESCRIPT-ARCHITECTURE.md` - Component patterns
- `47-THEMING.md` - Visual styling

---

*"The best keyboard interface is one that power users forget they're using."*
