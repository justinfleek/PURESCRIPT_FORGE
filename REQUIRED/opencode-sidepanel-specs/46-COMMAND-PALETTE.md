# 46-COMMAND-PALETTE: Universal Command Interface

## Overview

The Command Palette provides instant access to every action in the sidepanel through a searchable, keyboard-driven interface. Press `Ctrl+Shift+P` (or `Cmd+Shift+P` on Mac) to open.

---

## Design Principles

1. **Instant** - Opens in <50ms, results filter as you type
2. **Universal** - Every action accessible from one place
3. **Contextual** - Shows relevant commands based on current view
4. **Learnable** - Shows keyboard shortcuts alongside commands

---

## Visual Design

### Command Palette

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  > search commands...                                                │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  ┌─ RECENT ──────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ● Go to Dashboard                                              1     │ │
│  │  ● Create New Session                                     Ctrl+N      │ │
│  │  ● Toggle Sidebar                                              [     │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ NAVIGATION ──────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ○ Go to Dashboard                                              1     │ │
│  │  ○ Go to Session                                                2     │ │
│  │  ○ Go to Proofs                                                 3     │ │
│  │  ○ Go to Timeline                                               4     │ │
│  │  ○ Go to Settings                                               5     │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ↑↓ Navigate   ⏎ Select   Esc Close                                       │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Filtered Results

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  > session                                                           │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  ┌─ RESULTS (8) ─────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ● Go to Session                                                2     │ │
│  │  ○ Create New Session                                     Ctrl+N      │ │
│  │  ○ Export Session                                    Ctrl+Shift+E     │ │
│  │  ○ Branch Session                                              gb     │ │
│  │  ○ Archive Session                                                    │ │
│  │  ○ Delete Session                                                     │ │
│  │  ○ Session Settings                                                   │ │
│  │  ○ Compare Sessions                                                   │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  8 results for "session"                                                   │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Command Categories

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  > ?                                                                 │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  Type a prefix to filter by category:                                      │
│                                                                             │
│  ┌─ PREFIXES ────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  >      Commands (default)                                            │ │
│  │  @      Go to view                                                    │ │
│  │  #      Search sessions by tag                                        │ │
│  │  :      Go to line/message                                            │ │
│  │  /      Search in current view                                        │ │
│  │  ?      Show this help                                                │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Command Registry

### All Commands

```typescript
interface Command {
  id: string;
  title: string;
  category: CommandCategory;
  keywords: string[];  // Additional search terms
  shortcut?: string;
  icon?: string;
  
  // Execution
  action: () => void | Promise<void>;
  
  // Visibility
  when?: () => boolean;  // Context condition
  enabledWhen?: () => boolean;
}

type CommandCategory =
  | 'navigation'
  | 'session'
  | 'view'
  | 'edit'
  | 'proof'
  | 'export'
  | 'settings'
  | 'help';

const commands: Command[] = [
  // Navigation
  { id: 'nav.dashboard', title: 'Go to Dashboard', category: 'navigation', shortcut: '1', keywords: ['home', 'main'], action: () => navigate(Dashboard) },
  { id: 'nav.session', title: 'Go to Session', category: 'navigation', shortcut: '2', keywords: ['chat', 'conversation'], action: () => navigate(Session) },
  { id: 'nav.proofs', title: 'Go to Proofs', category: 'navigation', shortcut: '3', keywords: ['lean', 'theorem'], action: () => navigate(Proofs) },
  { id: 'nav.timeline', title: 'Go to Timeline', category: 'navigation', shortcut: '4', keywords: ['history', 'snapshots'], action: () => navigate(Timeline) },
  { id: 'nav.settings', title: 'Go to Settings', category: 'navigation', shortcut: '5', keywords: ['preferences', 'config'], action: () => navigate(Settings) },
  { id: 'nav.files', title: 'Go to Files', category: 'navigation', shortcut: 'gf', keywords: ['context', 'tokens'], action: () => navigate(Files) },
  { id: 'nav.recordings', title: 'Go to Recordings', category: 'navigation', shortcut: 'gr', keywords: ['playback', 'replay'], action: () => navigate(Recordings) },
  { id: 'nav.search', title: 'Open Search', category: 'navigation', shortcut: '/', keywords: ['find', 'query'], action: () => openSearch() },
  { id: 'nav.performance', title: 'Go to Performance', category: 'navigation', keywords: ['profiler', 'flame'], action: () => navigate(Performance) },
  
  // Session
  { id: 'session.new', title: 'Create New Session', category: 'session', shortcut: 'Ctrl+N', keywords: ['start', 'fresh'], action: () => createSession() },
  { id: 'session.branch', title: 'Branch Session', category: 'session', shortcut: 'gb', keywords: ['fork', 'split'], action: () => branchSession(), when: () => hasActiveSession() },
  { id: 'session.export', title: 'Export Session', category: 'session', shortcut: 'Ctrl+Shift+E', keywords: ['save', 'download'], action: () => exportSession(), when: () => hasActiveSession() },
  { id: 'session.archive', title: 'Archive Session', category: 'session', keywords: ['close', 'store'], action: () => archiveSession(), when: () => hasActiveSession() },
  { id: 'session.delete', title: 'Delete Session', category: 'session', keywords: ['remove', 'destroy'], action: () => deleteSession(), when: () => hasActiveSession() },
  
  // View
  { id: 'view.refresh', title: 'Refresh View', category: 'view', shortcut: 'r', keywords: ['reload', 'update'], action: () => refreshView() },
  { id: 'view.sidebar.toggle', title: 'Toggle Sidebar', category: 'view', shortcut: '[', keywords: ['collapse', 'expand'], action: () => toggleSidebar() },
  { id: 'view.fullscreen', title: 'Toggle Fullscreen', category: 'view', shortcut: 'F11', keywords: ['maximize'], action: () => toggleFullscreen() },
  { id: 'view.zoom.in', title: 'Zoom In', category: 'view', shortcut: 'Ctrl++', action: () => zoomIn() },
  { id: 'view.zoom.out', title: 'Zoom Out', category: 'view', shortcut: 'Ctrl+-', action: () => zoomOut() },
  { id: 'view.zoom.reset', title: 'Reset Zoom', category: 'view', shortcut: 'Ctrl+0', action: () => zoomReset() },
  
  // Proofs
  { id: 'proof.refresh', title: 'Refresh Proofs', category: 'proof', keywords: ['reload', 'check'], action: () => refreshProofs(), when: () => isProofView() },
  { id: 'proof.next', title: 'Next Goal', category: 'proof', shortcut: 'Tab', action: () => nextGoal(), when: () => isProofView() },
  { id: 'proof.prev', title: 'Previous Goal', category: 'proof', shortcut: 'Shift+Tab', action: () => prevGoal(), when: () => isProofView() },
  { id: 'proof.apply', title: 'Apply Tactic', category: 'proof', shortcut: 'a', action: () => applyTactic(), when: () => isProofView() },
  
  // Timeline
  { id: 'timeline.snapshot', title: 'Create Snapshot', category: 'session', shortcut: 'Ctrl+S', keywords: ['save', 'bookmark'], action: () => createSnapshot() },
  { id: 'timeline.restore', title: 'Restore Snapshot', category: 'session', keywords: ['rollback', 'revert'], action: () => restoreSnapshot(), when: () => hasSnapshots() },
  
  // Export
  { id: 'export.markdown', title: 'Export as Markdown', category: 'export', keywords: ['md', 'text'], action: () => exportAs('markdown') },
  { id: 'export.json', title: 'Export as JSON', category: 'export', keywords: ['data'], action: () => exportAs('json') },
  { id: 'export.copy', title: 'Copy to Clipboard', category: 'export', shortcut: 'Ctrl+Shift+C', keywords: ['clipboard'], action: () => copyToClipboard() },
  
  // Settings
  { id: 'settings.theme', title: 'Toggle Dark/Light Mode', category: 'settings', keywords: ['theme', 'appearance'], action: () => toggleTheme() },
  { id: 'settings.model', title: 'Change Model', category: 'settings', keywords: ['llm', 'ai'], action: () => openModelPicker() },
  { id: 'settings.keyboard', title: 'Keyboard Shortcuts', category: 'settings', shortcut: '?', keywords: ['keys', 'bindings'], action: () => showKeyboardShortcuts() },
  
  // Help
  { id: 'help.shortcuts', title: 'Show Keyboard Shortcuts', category: 'help', shortcut: '?', action: () => showKeyboardShortcuts() },
  { id: 'help.tour', title: 'Start Feature Tour', category: 'help', keywords: ['onboarding', 'guide'], action: () => startTour() },
  { id: 'help.docs', title: 'Open Documentation', category: 'help', keywords: ['manual', 'reference'], action: () => openDocs() },
  { id: 'help.about', title: 'About Sidepanel', category: 'help', keywords: ['version', 'info'], action: () => showAbout() },
];
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.CommandPalette where

import Prelude
import Data.Array (Array)
import Data.Maybe (Maybe)

type Command =
  { id :: String
  , title :: String
  , category :: String
  , keywords :: Array String
  , shortcut :: Maybe String
  , icon :: Maybe String
  }

type State =
  { isOpen :: Boolean
  , query :: String
  , results :: Array Command
  , selectedIndex :: Int
  , recentCommands :: Array String
  }

data Action
  = Open
  | Close
  | SetQuery String
  | SelectNext
  | SelectPrevious
  | ExecuteSelected
  | ExecuteCommand String
  | ClearRecent

data Output
  = CommandExecuted String
```

### Component

```purescript
component :: forall q m. MonadAff m => H.Component q Unit Output m
component = H.mkComponent
  { initialState: const initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction }
  }

initialState :: State
initialState =
  { isOpen: false
  , query: ""
  , results: []
  , selectedIndex: 0
  , recentCommands: []
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state
  | not state.isOpen = HH.text ""
  | otherwise =
      HH.div
        [ HP.class_ (H.ClassName "command-palette-overlay")
        , HE.onClick \_ -> Close
        ]
        [ HH.div
            [ HP.class_ (H.ClassName "command-palette")
            , HE.onClick (const Nothing)  -- Prevent close on palette click
            ]
            [ renderInput state
            , if state.query == ""
                then renderRecent state.recentCommands
                else renderResults state
            , renderFooter
            ]
        ]

renderInput :: forall m. State -> H.ComponentHTML Action () m
renderInput state =
  HH.div
    [ HP.class_ (H.ClassName "palette-input-container") ]
    [ HH.span [ HP.class_ (H.ClassName "palette-prompt") ] [ HH.text ">" ]
    , HH.input
        [ HP.class_ (H.ClassName "palette-input")
        , HP.placeholder "Type a command..."
        , HP.value state.query
        , HP.autofocus true
        , HE.onValueInput SetQuery
        , HE.onKeyDown handleKeyDown
        ]
    ]

renderResults :: forall m. State -> H.ComponentHTML Action () m
renderResults state =
  HH.div
    [ HP.class_ (H.ClassName "palette-results") ]
    [ HH.div
        [ HP.class_ (H.ClassName "results-header") ]
        [ HH.text $ "Results (" <> show (length state.results) <> ")" ]
    , HH.div
        [ HP.class_ (H.ClassName "results-list") ]
        (mapWithIndex (renderResult state.selectedIndex) state.results)
    ]

renderResult :: forall m. Int -> Int -> Command -> H.ComponentHTML Action () m
renderResult selectedIndex index cmd =
  HH.div
    [ HP.classes $ resultClasses (selectedIndex == index)
    , HE.onClick \_ -> ExecuteCommand cmd.id
    , HE.onMouseEnter \_ -> SetSelectedIndex index
    ]
    [ HH.span [ HP.class_ (H.ClassName "result-icon") ]
        [ HH.text $ fromMaybe "○" cmd.icon ]
    , HH.span [ HP.class_ (H.ClassName "result-title") ]
        [ HH.text cmd.title ]
    , case cmd.shortcut of
        Just shortcut ->
          HH.span [ HP.class_ (H.ClassName "result-shortcut") ]
            [ HH.text shortcut ]
        Nothing -> HH.text ""
    ]

handleKeyDown :: KeyboardEvent -> Maybe Action
handleKeyDown event = case key event of
  "ArrowDown" -> Just SelectNext
  "ArrowUp" -> Just SelectPrevious
  "Enter" -> Just ExecuteSelected
  "Escape" -> Just Close
  _ -> Nothing

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Open -> do
    H.modify_ _ { isOpen = true, query = "", selectedIndex = 0 }
  
  Close -> do
    H.modify_ _ { isOpen = false }
  
  SetQuery query -> do
    let results = filterCommands query allCommands
    H.modify_ _ { query = query, results = results, selectedIndex = 0 }
  
  SelectNext -> do
    state <- H.get
    let maxIndex = length state.results - 1
    H.modify_ \s -> s { selectedIndex = min maxIndex (s.selectedIndex + 1) }
  
  SelectPrevious -> do
    H.modify_ \s -> s { selectedIndex = max 0 (s.selectedIndex - 1) }
  
  ExecuteSelected -> do
    state <- H.get
    case state.results !! state.selectedIndex of
      Just cmd -> handleAction (ExecuteCommand cmd.id)
      Nothing -> pure unit
  
  ExecuteCommand cmdId -> do
    -- Add to recent
    H.modify_ \s -> s { recentCommands = take 5 (cmdId : filter (_ /= cmdId) s.recentCommands) }
    
    -- Execute and close
    executeCommand cmdId
    H.modify_ _ { isOpen = false }
    
    H.raise (CommandExecuted cmdId)
  
  _ -> pure unit

-- Fuzzy search
filterCommands :: String -> Array Command -> Array Command
filterCommands query commands
  | query == "" = commands
  | otherwise =
      commands
        # filter (matchesQuery query)
        # sortBy (compareScore query)

matchesQuery :: String -> Command -> Boolean
matchesQuery query cmd =
  let q = toLower query
      title = toLower cmd.title
      keywords = map toLower cmd.keywords
  in contains q title || any (contains q) keywords

compareScore :: String -> Command -> Command -> Ordering
compareScore query a b =
  compare (score query b) (score query a)

score :: String -> Command -> Int
score query cmd
  | startsWith (toLower query) (toLower cmd.title) = 100
  | contains (toLower query) (toLower cmd.title) = 50
  | any (contains (toLower query)) (map toLower cmd.keywords) = 25
  | otherwise = 0
```

---

## CSS Styling

```css
.command-palette-overlay {
  position: fixed;
  inset: 0;
  background: rgba(0, 0, 0, 0.5);
  display: flex;
  justify-content: center;
  padding-top: 15vh;
  z-index: 1000;
  animation: fadeIn 0.1s ease-out;
}

.command-palette {
  width: 100%;
  max-width: 600px;
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-default);
  border-radius: 12px;
  box-shadow: var(--shadow-2xl);
  overflow: hidden;
  animation: slideDown 0.15s ease-out;
}

@keyframes slideDown {
  from {
    opacity: 0;
    transform: translateY(-20px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

.palette-input-container {
  display: flex;
  align-items: center;
  padding: var(--space-4);
  border-bottom: 1px solid var(--color-border-subtle);
}

.palette-prompt {
  color: var(--color-primary);
  font-family: var(--font-mono);
  font-size: var(--font-size-lg);
  margin-right: var(--space-2);
}

.palette-input {
  flex: 1;
  background: transparent;
  border: none;
  outline: none;
  font-size: var(--font-size-lg);
  color: var(--color-text-primary);
}

.palette-input::placeholder {
  color: var(--color-text-tertiary);
}

.palette-results {
  max-height: 400px;
  overflow-y: auto;
}

.results-header {
  padding: var(--space-2) var(--space-4);
  font-size: var(--font-size-xs);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-tertiary);
  text-transform: uppercase;
  letter-spacing: var(--letter-spacing-wider);
  background: var(--color-bg-elevated);
}

.results-list {
  padding: var(--space-2);
}

.result-item {
  display: flex;
  align-items: center;
  gap: var(--space-3);
  padding: var(--space-2) var(--space-3);
  border-radius: 6px;
  cursor: pointer;
  transition: background var(--transition-fast);
}

.result-item:hover,
.result-item--selected {
  background: var(--color-bg-hover);
}

.result-item--selected {
  background: var(--color-primary-dim);
}

.result-icon {
  width: 20px;
  text-align: center;
  color: var(--color-text-tertiary);
}

.result-title {
  flex: 1;
  color: var(--color-text-primary);
}

.result-shortcut {
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
  padding: 2px 6px;
  background: var(--color-bg-base);
  border: 1px solid var(--color-border-subtle);
  border-radius: 4px;
}

.palette-footer {
  padding: var(--space-2) var(--space-4);
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
  background: var(--color-bg-elevated);
  border-top: 1px solid var(--color-border-subtle);
  display: flex;
  gap: var(--space-4);
}
```

---

## Related Specifications

- `48-KEYBOARD-NAVIGATION.md` - Keyboard system
- `68-HELP-OVERLAY.md` - Shortcut reference
- `45-ROUTING.md` - Navigation actions

---

*"Every action, one keystroke away."*
