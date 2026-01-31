# 57-TERMINAL-EMBED: Integrated Terminal View

## Overview

The Terminal Embed provides a fully functional terminal within the sidepanel using xterm.js, allowing users to see OpenCode's terminal output without switching windows.

---

## Why Embedded Terminal?

1. **Context retention** - See AI conversation AND terminal output together
2. **No window switching** - Everything in one view
3. **Output correlation** - Match AI suggestions to terminal results
4. **Quick commands** - Run tests, git, etc. without leaving

---

## Visual Design

### Terminal Panel

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  TERMINAL                              [Clear] [Copy] [↗ Detach] [Settings] │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌───────────────────────────────────────────────────────────────────────┐ │
│  │ $ opencode                                                             │ │
│  │ OpenCode v0.5.0 - AI Coding Assistant                                 │ │
│  │ Model: llama-3.3-70b (Venice)                                         │ │
│  │ Session: Debug Auth                                                    │ │
│  │                                                                        │ │
│  │ You: Help me debug this authentication flow                           │ │
│  │                                                                        │ │
│  │ Assistant: I'll analyze the authentication code. Let me start by     │ │
│  │ reading the relevant files.                                           │ │
│  │                                                                        │ │
│  │ [Reading src/auth/session.ts...]                                      │ │
│  │ [Reading src/auth/middleware.ts...]                                   │ │
│  │                                                                        │ │
│  │ I found the issue. In session.ts line 42, the token expiration       │ │
│  │ check is using local time instead of UTC. This causes random         │ │
│  │ logouts for users in different timezones.                            │ │
│  │                                                                        │ │
│  │ Would you like me to fix it?                                         │ │
│  │                                                                        │ │
│  │ You: Yes, please fix it and add a test                               │ │
│  │ █                                                                      │ │
│  └───────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ QUICK COMMANDS ──────────────────────────────────────────────────────┐ │
│  │  [npm test] [git status] [git diff] [clear] [Custom...]               │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Split View (Terminal + Session)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  SESSION + TERMINAL                                             [Layout ▼] │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ SESSION ─────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  👤 Help me debug this authentication flow                            │ │
│  │                                                                        │ │
│  │  🤖 I found the issue in session.ts line 42...                        │ │
│  │     [Show more]                                                        │ │
│  │                                                                        │ │
│  │  👤 Yes, please fix it and add a test                                 │ │
│  │                                                                        │ │
│  │  🤖 Done! I've fixed the timezone bug and added tests.                │ │
│  │     Modified: src/auth/session.ts                                     │ │
│  │     Created: src/auth/session.test.ts                                 │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│  ═══════════════════════════════════════════════════════════════════════════│
│  ┌─ TERMINAL ────────────────────────────────────────────────────────────┐ │
│  │ $ npm test src/auth/session.test.ts                                   │ │
│  │                                                                        │ │
│  │  PASS  src/auth/session.test.ts                                       │ │
│  │   isTokenValid                                                        │ │
│  │     ✓ returns true for valid token (3ms)                              │ │
│  │     ✓ returns false for expired token (1ms)                           │ │
│  │     ✓ handles timezone correctly (2ms)                                │ │
│  │                                                                        │ │
│  │ Test Suites: 1 passed, 1 total                                        │ │
│  │ Tests:       3 passed, 3 total                                        │ │
│  │                                                                        │ │
│  │ $ █                                                                    │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Technical Implementation

### xterm.js Integration

```typescript
// frontend/src/FFI/Terminal.ts
import { Terminal } from 'xterm';
import { FitAddon } from 'xterm-addon-fit';
import { WebLinksAddon } from 'xterm-addon-web-links';
import { SearchAddon } from 'xterm-addon-search';

export interface TerminalConfig {
  fontSize: number;
  fontFamily: string;
  theme: TerminalTheme;
  cursorBlink: boolean;
  scrollback: number;
}

export interface TerminalTheme {
  background: string;
  foreground: string;
  cursor: string;
  cursorAccent: string;
  selection: string;
  black: string;
  red: string;
  green: string;
  yellow: string;
  blue: string;
  magenta: string;
  cyan: string;
  white: string;
  brightBlack: string;
  brightRed: string;
  brightGreen: string;
  brightYellow: string;
  brightBlue: string;
  brightMagenta: string;
  brightCyan: string;
  brightWhite: string;
}

export class TerminalManager {
  private terminal: Terminal;
  private fitAddon: FitAddon;
  private searchAddon: SearchAddon;
  private ws: WebSocket | null = null;
  private container: HTMLElement | null = null;
  
  constructor(config: TerminalConfig) {
    this.terminal = new Terminal({
      fontSize: config.fontSize,
      fontFamily: config.fontFamily,
      theme: config.theme,
      cursorBlink: config.cursorBlink,
      scrollback: config.scrollback,
      allowProposedApi: true
    });
    
    this.fitAddon = new FitAddon();
    this.searchAddon = new SearchAddon();
    
    this.terminal.loadAddon(this.fitAddon);
    this.terminal.loadAddon(this.searchAddon);
    this.terminal.loadAddon(new WebLinksAddon());
  }
  
  mount(container: HTMLElement): void {
    this.container = container;
    this.terminal.open(container);
    this.fitAddon.fit();
    
    // Handle resize
    const resizeObserver = new ResizeObserver(() => {
      this.fitAddon.fit();
    });
    resizeObserver.observe(container);
  }
  
  connectToPty(wsUrl: string): void {
    this.ws = new WebSocket(wsUrl);
    
    this.ws.onmessage = (event) => {
      this.terminal.write(event.data);
    };
    
    this.terminal.onData((data) => {
      this.ws?.send(JSON.stringify({ type: 'input', data }));
    });
    
    this.terminal.onResize(({ cols, rows }) => {
      this.ws?.send(JSON.stringify({ type: 'resize', cols, rows }));
    });
  }
  
  write(data: string): void {
    this.terminal.write(data);
  }
  
  clear(): void {
    this.terminal.clear();
  }
  
  search(query: string): boolean {
    return this.searchAddon.findNext(query);
  }
  
  scrollToBottom(): void {
    this.terminal.scrollToBottom();
  }
  
  focus(): void {
    this.terminal.focus();
  }
  
  dispose(): void {
    this.ws?.close();
    this.terminal.dispose();
  }
  
  getSelection(): string {
    return this.terminal.getSelection();
  }
  
  copySelection(): void {
    const selection = this.getSelection();
    if (selection) {
      navigator.clipboard.writeText(selection);
    }
  }
}
```

### PureScript FFI Bindings

```purescript
-- frontend/src/Sidepanel/FFI/Terminal.purs
module Sidepanel.FFI.Terminal where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Web.HTML.HTMLElement (HTMLElement)

foreign import data TerminalManager :: Type

type TerminalConfig =
  { fontSize :: Int
  , fontFamily :: String
  , cursorBlink :: Boolean
  , scrollback :: Int
  }

foreign import createTerminal :: TerminalConfig -> Effect TerminalManager

foreign import mountTerminal :: TerminalManager -> HTMLElement -> Effect Unit

foreign import connectToPty :: TerminalManager -> String -> Effect Unit

foreign import writeToTerminal :: TerminalManager -> String -> Effect Unit

foreign import clearTerminal :: TerminalManager -> Effect Unit

foreign import searchTerminal :: TerminalManager -> String -> Effect Boolean

foreign import focusTerminal :: TerminalManager -> Effect Unit

foreign import disposeTerminal :: TerminalManager -> Effect Unit

foreign import getTerminalSelection :: TerminalManager -> Effect String

foreign import copyTerminalSelection :: TerminalManager -> Effect Unit
```

### FFI Implementation

```javascript
// frontend/src/Sidepanel/FFI/Terminal.js
import { TerminalManager } from './Terminal.ts';

export function createTerminal(config) {
  return function() {
    return new TerminalManager(config);
  };
}

export function mountTerminal(terminal) {
  return function(element) {
    return function() {
      terminal.mount(element);
    };
  };
}

export function connectToPty(terminal) {
  return function(wsUrl) {
    return function() {
      terminal.connectToPty(wsUrl);
    };
  };
}

export function writeToTerminal(terminal) {
  return function(data) {
    return function() {
      terminal.write(data);
    };
  };
}

export function clearTerminal(terminal) {
  return function() {
    terminal.clear();
  };
}

export function searchTerminal(terminal) {
  return function(query) {
    return function() {
      return terminal.search(query);
    };
  };
}

export function focusTerminal(terminal) {
  return function() {
    terminal.focus();
  };
}

export function disposeTerminal(terminal) {
  return function() {
    terminal.dispose();
  };
}

export function getTerminalSelection(terminal) {
  return function() {
    return terminal.getSelection();
  };
}

export function copyTerminalSelection(terminal) {
  return function() {
    terminal.copySelection();
  };
}
```

---

## Halogen Component

```purescript
module Sidepanel.Components.Terminal where

import Prelude
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Web.HTML.HTMLElement (HTMLElement)
import Sidepanel.FFI.Terminal as FFI

type State =
  { terminal :: Maybe FFI.TerminalManager
  , isConnected :: Boolean
  , searchQuery :: String
  , isSearchVisible :: Boolean
  }

data Action
  = Initialize
  | Finalize
  | SetContainerRef HTMLElement
  | ConnectToPty String
  | Write String
  | Clear
  | Copy
  | ToggleSearch
  | SetSearchQuery String
  | SearchNext
  | SearchPrevious

data Query a
  = WriteQ String a
  | ClearQ a
  | FocusQ a

component :: forall i o m. MonadAff m => H.Component Query i o m
component = H.mkComponent
  { initialState: const initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      , finalize = Just Finalize
      }
  }

initialState :: State
initialState =
  { terminal: Nothing
  , isConnected: false
  , searchQuery: ""
  , isSearchVisible: false
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "terminal-container") ]
    [ -- Toolbar
      renderToolbar state
    
    -- Search bar (if visible)
    , when state.isSearchVisible $ renderSearchBar state
    
    -- Terminal element
    , HH.div
        [ HP.class_ (H.ClassName "terminal-viewport")
        , HP.ref (H.RefLabel "terminal-container")
        ]
        []
    
    -- Quick commands
    , renderQuickCommands
    ]

renderToolbar :: forall m. State -> H.ComponentHTML Action () m
renderToolbar state =
  HH.div
    [ HP.class_ (H.ClassName "terminal-toolbar") ]
    [ HH.span
        [ HP.class_ (H.ClassName "terminal-toolbar__title") ]
        [ HH.text "Terminal" ]
    , HH.div
        [ HP.class_ (H.ClassName "terminal-toolbar__actions") ]
        [ HH.button
            [ HP.class_ (H.ClassName "btn btn--icon")
            , HP.title "Search (Ctrl+F)"
            , HE.onClick \_ -> ToggleSearch
            ]
            [ HH.text "🔍" ]
        , HH.button
            [ HP.class_ (H.ClassName "btn btn--icon")
            , HP.title "Clear"
            , HE.onClick \_ -> Clear
            ]
            [ HH.text "⌫" ]
        , HH.button
            [ HP.class_ (H.ClassName "btn btn--icon")
            , HP.title "Copy Selection"
            , HE.onClick \_ -> Copy
            ]
            [ HH.text "📋" ]
        ]
    ]

renderSearchBar :: forall m. State -> H.ComponentHTML Action () m
renderSearchBar state =
  HH.div
    [ HP.class_ (H.ClassName "terminal-search") ]
    [ HH.input
        [ HP.type_ HP.InputText
        , HP.placeholder "Search..."
        , HP.value state.searchQuery
        , HP.class_ (H.ClassName "terminal-search__input")
        , HE.onValueInput SetSearchQuery
        ]
    , HH.button
        [ HP.class_ (H.ClassName "btn btn--sm")
        , HE.onClick \_ -> SearchPrevious
        ]
        [ HH.text "↑" ]
    , HH.button
        [ HP.class_ (H.ClassName "btn btn--sm")
        , HE.onClick \_ -> SearchNext
        ]
        [ HH.text "↓" ]
    , HH.button
        [ HP.class_ (H.ClassName "btn btn--sm")
        , HE.onClick \_ -> ToggleSearch
        ]
        [ HH.text "✕" ]
    ]

renderQuickCommands :: forall m. H.ComponentHTML Action () m
renderQuickCommands =
  HH.div
    [ HP.class_ (H.ClassName "terminal-quick-commands") ]
    [ HH.button
        [ HP.class_ (H.ClassName "quick-cmd")
        , HE.onClick \_ -> Write "npm test\n"
        ]
        [ HH.text "npm test" ]
    , HH.button
        [ HP.class_ (H.ClassName "quick-cmd")
        , HE.onClick \_ -> Write "git status\n"
        ]
        [ HH.text "git status" ]
    , HH.button
        [ HP.class_ (H.ClassName "quick-cmd")
        , HE.onClick \_ -> Write "git diff\n"
        ]
        [ HH.text "git diff" ]
    , HH.button
        [ HP.class_ (H.ClassName "quick-cmd")
        , HE.onClick \_ -> Clear
        ]
        [ HH.text "clear" ]
    ]

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Initialize -> do
    -- Create terminal
    terminal <- H.liftEffect $ FFI.createTerminal defaultConfig
    H.modify_ _ { terminal = Just terminal }
    
    -- Get container ref and mount
    mContainer <- H.getHTMLElementRef (H.RefLabel "terminal-container")
    for_ mContainer \container -> do
      H.liftEffect $ FFI.mountTerminal terminal container
      -- Connect to bridge PTY
      H.liftEffect $ FFI.connectToPty terminal "ws://localhost:3000/pty"
      H.modify_ _ { isConnected = true }
  
  Finalize -> do
    state <- H.get
    for_ state.terminal \terminal ->
      H.liftEffect $ FFI.disposeTerminal terminal
  
  Write text -> do
    state <- H.get
    for_ state.terminal \terminal ->
      H.liftEffect $ FFI.writeToTerminal terminal text
  
  Clear -> do
    state <- H.get
    for_ state.terminal \terminal ->
      H.liftEffect $ FFI.clearTerminal terminal
  
  Copy -> do
    state <- H.get
    for_ state.terminal \terminal ->
      H.liftEffect $ FFI.copyTerminalSelection terminal
  
  ToggleSearch ->
    H.modify_ \s -> s { isSearchVisible = not s.isSearchVisible }
  
  SetSearchQuery query -> do
    H.modify_ _ { searchQuery = query }
    when (String.length query >= 2) do
      state <- H.get
      for_ state.terminal \terminal ->
        void $ H.liftEffect $ FFI.searchTerminal terminal query
  
  SearchNext -> do
    state <- H.get
    for_ state.terminal \terminal ->
      void $ H.liftEffect $ FFI.searchTerminal terminal state.searchQuery
  
  _ -> pure unit

handleQuery :: forall o m a. MonadAff m => Query a -> H.HalogenM State Action () o m (Maybe a)
handleQuery = case _ of
  WriteQ text next -> do
    handleAction (Write text)
    pure $ Just next
  
  ClearQ next -> do
    handleAction Clear
    pure $ Just next
  
  FocusQ next -> do
    state <- H.get
    for_ state.terminal \terminal ->
      H.liftEffect $ FFI.focusTerminal terminal
    pure $ Just next

defaultConfig :: FFI.TerminalConfig
defaultConfig =
  { fontSize: 13
  , fontFamily: "JetBrains Mono, monospace"
  , cursorBlink: true
  , scrollback: 10000
  }
```

---

## Terminal Theme

```typescript
// Theme matching sidepanel dark mode
export const terminalTheme: TerminalTheme = {
  background: '#0d0d0d',
  foreground: '#e4e4e7',
  cursor: '#8b5cf6',
  cursorAccent: '#0d0d0d',
  selection: 'rgba(139, 92, 246, 0.3)',
  
  // Standard colors
  black: '#18181b',
  red: '#ef4444',
  green: '#22c55e',
  yellow: '#f59e0b',
  blue: '#3b82f6',
  magenta: '#8b5cf6',
  cyan: '#06b6d4',
  white: '#e4e4e7',
  
  // Bright colors
  brightBlack: '#71717a',
  brightRed: '#f87171',
  brightGreen: '#4ade80',
  brightYellow: '#fbbf24',
  brightBlue: '#60a5fa',
  brightMagenta: '#a78bfa',
  brightCyan: '#22d3ee',
  brightWhite: '#fafafa'
};
```

---

## CSS Styling

```css
.terminal-container {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--color-bg-base);
}

.terminal-toolbar {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: var(--space-2) var(--space-3);
  background: var(--color-bg-elevated);
  border-bottom: 1px solid var(--color-border-subtle);
}

.terminal-toolbar__title {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  font-weight: var(--font-weight-medium);
}

.terminal-toolbar__actions {
  display: flex;
  gap: var(--space-1);
}

.terminal-viewport {
  flex: 1;
  overflow: hidden;
  padding: var(--space-2);
}

.terminal-viewport .xterm {
  height: 100%;
}

.terminal-viewport .xterm-viewport {
  overflow-y: auto;
}

.terminal-search {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  padding: var(--space-2) var(--space-3);
  background: var(--color-bg-surface);
  border-bottom: 1px solid var(--color-border-subtle);
}

.terminal-search__input {
  flex: 1;
  padding: var(--space-1) var(--space-2);
  background: var(--color-bg-base);
  border: 1px solid var(--color-border-subtle);
  border-radius: 4px;
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-text-primary);
}

.terminal-quick-commands {
  display: flex;
  gap: var(--space-2);
  padding: var(--space-2) var(--space-3);
  background: var(--color-bg-surface);
  border-top: 1px solid var(--color-border-subtle);
  overflow-x: auto;
}

.quick-cmd {
  padding: var(--space-1) var(--space-2);
  background: var(--color-bg-elevated);
  border: 1px solid var(--color-border-subtle);
  border-radius: 4px;
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  color: var(--color-text-secondary);
  white-space: nowrap;
  cursor: pointer;
  transition: all var(--transition-fast);
}

.quick-cmd:hover {
  background: var(--color-bg-hover);
  border-color: var(--color-primary);
  color: var(--color-primary);
}
```

---

## Related Specifications

- `47-THEMING.md` - Color tokens
- `44-FFI-BINDINGS.md` - FFI patterns
- `54-SESSION-PANEL.md` - Session integration

---

*"The terminal is where work happens. Keep it close."*
