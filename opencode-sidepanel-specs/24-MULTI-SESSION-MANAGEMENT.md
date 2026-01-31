# 24-MULTI-SESSION-MANAGEMENT: Tabs, Branching, and Parallel Conversations

## Overview

The sidepanel supports multiple concurrent AI sessions with tabbed navigation, session branching (fork a conversation to try different approaches), and session comparison.

---

## Why Multi-Session?

Real coding workflows aren't linear:

1. **Parallel exploration** - "Try approach A in one session, approach B in another"
2. **Context separation** - "Debug session vs. refactor session vs. docs session"
3. **Branching decisions** - "Fork here to see what happens if I ask differently"
4. **Comparison** - "Which approach used fewer tokens?"

---

## Visual Design

### Session Tabs

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ [🔧 Debug Auth ✕] [📝 Tests ✕] [🔬 Proofs ✕] [📄 Docs] [+]          │   │
│  │       ▲ active                                                       │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  Session content here...                                                    │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Session Branching

```
                    ┌─────────────────────┐
                    │ Original Session    │
                    │ Messages 1-5        │
                    └──────────┬──────────┘
                               │
                    ┌──────────┴──────────┐
                    │ Message 6           │
                    │ "Can you fix it?"   │
                    └──────────┬──────────┘
                               │
              ┌────────────────┼────────────────┐
              │                │                │
              ▼                ▼                ▼
     ┌─────────────┐  ┌─────────────┐  ┌─────────────┐
     │ Branch A    │  │ Original    │  │ Branch B    │
     │ "Fix with   │  │ Continued   │  │ "Fix with   │
     │  hooks"     │  │             │  │  classes"   │
     └─────────────┘  └─────────────┘  └─────────────┘
```

---

## Data Model

### Session Types

```typescript
// bridge/src/types/session.ts

interface Session {
  id: string;
  
  // Metadata
  title: string;
  icon: string;  // Emoji
  color?: string;
  createdAt: Date;
  updatedAt: Date;
  
  // Model info
  model: string;
  provider: string;
  
  // Branching
  parentId: string | null;      // If branched, points to parent
  branchPoint: number | null;   // Message index where branched
  children: string[];           // Child branch IDs
  
  // State
  status: SessionStatus;
  
  // Aggregates
  messageCount: number;
  promptTokens: number;
  completionTokens: number;
  cost: number;
}

type SessionStatus = 
  | 'active'      // Currently in use
  | 'idle'        // Open but not active
  | 'archived'    // Stored but hidden
  | 'deleted';    // Soft deleted

interface SessionBranch {
  id: string;
  parentSessionId: string;
  branchPointMessageId: string;
  branchPointIndex: number;
  createdAt: Date;
  description: string;
}
```

### Tab State

```purescript
module Sidepanel.State.Sessions where

type SessionTab =
  { sessionId :: String
  , title :: String
  , icon :: String
  , isActive :: Boolean
  , isDirty :: Boolean    -- Has unsaved changes
  , isPinned :: Boolean
  }

type SessionTabsState =
  { tabs :: Array SessionTab
  , activeTabId :: Maybe String
  , maxTabs :: Int           -- Default 10
  , tabOrder :: Array String -- IDs in display order
  }

data SessionAction
  = OpenSession String
  | CloseSession String
  | SwitchToSession String
  | ReorderTabs (Array String)
  | PinSession String
  | UnpinSession String
  | RenameSession String String
  | SetSessionIcon String String
  | CreateBranch String Int String  -- sessionId, messageIndex, description
  | MergeBranch String String       -- sourceId, targetId
```

---

## PureScript Implementation

### Session Tabs Component

```purescript
module Sidepanel.Components.Session.Tabs where

import Prelude
import Data.Array (mapWithIndex, filter, length)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

type Input =
  { tabs :: Array SessionTab
  , activeId :: Maybe String
  }

type State =
  { tabs :: Array SessionTab
  , activeId :: Maybe String
  , draggedId :: Maybe String
  , dropTargetId :: Maybe String
  }

data Action
  = Receive Input
  | SelectTab String
  | CloseTab String
  | StartDrag String
  | DragOver String
  | Drop
  | NewTab

data Output
  = TabSelected String
  | TabClosed String
  | TabsReordered (Array String)
  | NewTabRequested

component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      }
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "session-tabs") ]
    [ HH.div
        [ HP.class_ (H.ClassName "session-tabs__list")
        , HP.attr (H.AttrName "role") "tablist"
        ]
        (map (renderTab state) state.tabs <> [renderNewTabButton])
    ]

renderTab :: forall m. State -> SessionTab -> H.ComponentHTML Action () m
renderTab state tab =
  let 
    isActive = state.activeId == Just tab.sessionId
    isDragging = state.draggedId == Just tab.sessionId
    isDropTarget = state.dropTargetId == Just tab.sessionId
  in
    HH.div
      [ HP.classes $ tabClasses isActive isDragging isDropTarget
      , HP.attr (H.AttrName "role") "tab"
      , HP.attr (H.AttrName "aria-selected") (if isActive then "true" else "false")
      , HP.draggable true
      , HE.onClick \_ -> SelectTab tab.sessionId
      , HE.onDragStart \_ -> StartDrag tab.sessionId
      , HE.onDragOver \e -> do
          H.liftEffect $ preventDefault e
          DragOver tab.sessionId
      , HE.onDrop \_ -> Drop
      ]
      [ -- Icon
        HH.span [ HP.class_ (H.ClassName "tab__icon") ] [ HH.text tab.icon ]
      
      -- Title
      , HH.span [ HP.class_ (H.ClassName "tab__title") ] [ HH.text tab.title ]
      
      -- Dirty indicator
      , when tab.isDirty $
          HH.span [ HP.class_ (H.ClassName "tab__dirty") ] [ HH.text "●" ]
      
      -- Close button (not for pinned)
      , unless tab.isPinned $
          HH.button
            [ HP.class_ (H.ClassName "tab__close")
            , HE.onClick \e -> do
                H.liftEffect $ stopPropagation e
                CloseTab tab.sessionId
            ]
            [ HH.text "✕" ]
      ]

renderNewTabButton :: forall m. H.ComponentHTML Action () m
renderNewTabButton =
  HH.button
    [ HP.class_ (H.ClassName "session-tabs__new")
    , HE.onClick \_ -> NewTab
    ]
    [ HH.text "+" ]

tabClasses :: Boolean -> Boolean -> Boolean -> Array H.ClassName
tabClasses isActive isDragging isDropTarget =
  [ H.ClassName "session-tab" ]
  <> (if isActive then [H.ClassName "session-tab--active"] else [])
  <> (if isDragging then [H.ClassName "session-tab--dragging"] else [])
  <> (if isDropTarget then [H.ClassName "session-tab--drop-target"] else [])
```

### Branch Dialog Component

```purescript
module Sidepanel.Components.Session.BranchDialog where

type State =
  { sessionId :: String
  , messageIndex :: Int
  , description :: String
  , isCreating :: Boolean
  }

data Action
  = SetDescription String
  | CreateBranch
  | Cancel

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "branch-dialog") ]
    [ HH.div
        [ HP.class_ (H.ClassName "branch-dialog__header") ]
        [ HH.text "Create Branch" ]
    
    , HH.p_
        [ HH.text $ "Fork conversation from message " <> show (state.messageIndex + 1) ]
    
    , HH.div
        [ HP.class_ (H.ClassName "branch-dialog__field") ]
        [ HH.label_ [ HH.text "Description (optional)" ]
        , HH.input
            [ HP.type_ HP.InputText
            , HP.placeholder "e.g., 'Try with hooks instead'"
            , HP.value state.description
            , HE.onValueInput SetDescription
            ]
        ]
    
    , HH.div
        [ HP.class_ (H.ClassName "branch-dialog__actions") ]
        [ HH.button
            [ HP.class_ (H.ClassName "btn btn--secondary")
            , HE.onClick \_ -> Cancel
            ]
            [ HH.text "Cancel" ]
        , HH.button
            [ HP.classes [H.ClassName "btn", H.ClassName "btn--primary"]
            , HP.disabled state.isCreating
            , HE.onClick \_ -> CreateBranch
            ]
            [ HH.text $ if state.isCreating then "Creating..." else "Create Branch" ]
        ]
    ]
```

---

## Session Comparison View

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  COMPARE SESSIONS                                              [Close]      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────┐  ┌─────────────────────────────┐          │
│  │ Session A: "Try with hooks" │  │ Session B: "Try with classes"│          │
│  ├─────────────────────────────┤  ├─────────────────────────────┤          │
│  │ Messages: 8                 │  │ Messages: 12                │          │
│  │ Tokens: 12,456              │  │ Tokens: 18,234              │          │
│  │ Cost: $0.008                │  │ Cost: $0.012                │          │
│  │ Duration: 12 min            │  │ Duration: 18 min            │          │
│  │ Files changed: 3            │  │ Files changed: 5            │          │
│  └─────────────────────────────┘  └─────────────────────────────┘          │
│                                                                             │
│  DIVERGENCE POINT: Message 6                                               │
│  ───────────────────────────────────────────────────────────────────────── │
│                                                                             │
│  ┌─────────────────────────────┐  ┌─────────────────────────────┐          │
│  │ 👤 "Can you fix it using   │  │ 👤 "Can you fix it using    │          │
│  │     React hooks?"          │  │     class components?"       │          │
│  └─────────────────────────────┘  └─────────────────────────────┘          │
│                                                                             │
│  [Merge A into B]  [Merge B into A]  [Keep Both]  [Delete One]             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Bridge Session Management

```typescript
// bridge/src/sessions/manager.ts

export class SessionManager {
  private db: Database;
  private activeSession: Session | null = null;
  private openSessions: Map<string, Session> = new Map();
  
  async createSession(options: CreateSessionOptions): Promise<Session> {
    const session: Session = {
      id: generateId(),
      title: options.title ?? 'New Session',
      icon: options.icon ?? '💬',
      createdAt: new Date(),
      updatedAt: new Date(),
      model: options.model,
      provider: options.provider,
      parentId: null,
      branchPoint: null,
      children: [],
      status: 'active',
      messageCount: 0,
      promptTokens: 0,
      completionTokens: 0,
      cost: 0
    };
    
    await this.db.insertSession(session);
    this.openSessions.set(session.id, session);
    
    return session;
  }
  
  async createBranch(
    sourceSessionId: string, 
    messageIndex: number,
    description: string
  ): Promise<Session> {
    const source = await this.getSession(sourceSessionId);
    if (!source) throw new Error('Source session not found');
    
    // Get messages up to branch point
    const messages = await this.getMessages(sourceSessionId, 0, messageIndex);
    
    // Create new session
    const branch: Session = {
      id: generateId(),
      title: description || `Branch of ${source.title}`,
      icon: '🔀',
      createdAt: new Date(),
      updatedAt: new Date(),
      model: source.model,
      provider: source.provider,
      parentId: sourceSessionId,
      branchPoint: messageIndex,
      children: [],
      status: 'active',
      messageCount: messages.length,
      promptTokens: this.sumTokens(messages, 'prompt'),
      completionTokens: this.sumTokens(messages, 'completion'),
      cost: this.sumCost(messages)
    };
    
    await this.db.insertSession(branch);
    
    // Copy messages to branch
    for (const msg of messages) {
      await this.db.insertMessage({ ...msg, sessionId: branch.id });
    }
    
    // Update parent's children
    source.children.push(branch.id);
    await this.db.updateSession(source.id, { children: source.children });
    
    return branch;
  }
  
  async mergeBranch(sourceId: string, targetId: string): Promise<void> {
    const source = await this.getSession(sourceId);
    const target = await this.getSession(targetId);
    
    if (!source || !target) throw new Error('Session not found');
    if (source.parentId !== target.id && target.parentId !== source.id) {
      throw new Error('Can only merge parent-child sessions');
    }
    
    // Get messages after divergence point
    const branchPoint = source.branchPoint ?? target.branchPoint ?? 0;
    const sourceMessages = await this.getMessages(sourceId, branchPoint);
    
    // Append to target
    for (const msg of sourceMessages) {
      await this.db.insertMessage({ ...msg, sessionId: targetId });
    }
    
    // Archive source
    await this.db.updateSession(sourceId, { status: 'archived' });
  }
}
```

---

## CSS Styling

```css
.session-tabs {
  background: var(--color-bg-surface);
  border-bottom: 1px solid var(--color-border-subtle);
}

.session-tabs__list {
  display: flex;
  overflow-x: auto;
  scrollbar-width: none;
}

.session-tabs__list::-webkit-scrollbar {
  display: none;
}

.session-tab {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  padding: var(--space-2) var(--space-3);
  background: transparent;
  border: none;
  border-bottom: 2px solid transparent;
  color: var(--color-text-secondary);
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  cursor: pointer;
  white-space: nowrap;
  transition: all var(--transition-fast);
}

.session-tab:hover {
  background: var(--color-bg-hover);
  color: var(--color-text-primary);
}

.session-tab--active {
  color: var(--color-primary);
  border-bottom-color: var(--color-primary);
  background: var(--color-primary-dim);
}

.session-tab--dragging {
  opacity: 0.5;
}

.session-tab--drop-target {
  border-left: 2px solid var(--color-primary);
}

.tab__icon {
  font-size: 14px;
}

.tab__dirty {
  color: var(--color-warning);
  font-size: 8px;
}

.tab__close {
  padding: 2px 4px;
  background: transparent;
  border: none;
  color: var(--color-text-tertiary);
  cursor: pointer;
  border-radius: 4px;
}

.tab__close:hover {
  background: var(--color-bg-elevated);
  color: var(--color-text-primary);
}

.session-tabs__new {
  padding: var(--space-2) var(--space-3);
  background: transparent;
  border: none;
  color: var(--color-text-tertiary);
  font-size: var(--font-size-lg);
  cursor: pointer;
}

.session-tabs__new:hover {
  color: var(--color-primary);
}
```

---

## Keyboard Shortcuts

| Key | Action |
|-----|--------|
| `Ctrl+T` | New session tab |
| `Ctrl+W` | Close current tab |
| `Ctrl+Tab` | Next tab |
| `Ctrl+Shift+Tab` | Previous tab |
| `Ctrl+1-9` | Switch to tab 1-9 |
| `Ctrl+Shift+B` | Branch from current message |

---

## Related Specifications

- `23-SESSION-MANAGEMENT.md` - Session lifecycle
- `54-SESSION-PANEL.md` - Session detail view
- `34-DATABASE-SCHEMA.md` - Storage schema

---

*"Branches let you explore without fear. Tabs keep you organized."*
