# 54-SESSION-PANEL: Session Details View

## Overview

The Session Panel displays detailed information about the current or selected coding session, including message history, token usage breakdown, and session controls.

---

## Visual Design

### Layout

```
┌─────────────────────────────────────────────────────────────────────────┐
│  SESSION DETAILS                                        [Export] [Clear]│
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │  Current Session                                                   │  │
│  │                                                                    │  │
│  │  Model: llama-3.3-70b          Started: 2:34 PM                   │  │
│  │  Provider: Venice              Duration: 47 min                    │  │
│  │                                                                    │  │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐            │  │
│  │  │   15,234     │  │    8,721     │  │   $0.014     │            │  │
│  │  │   Prompt     │  │  Completion  │  │    Cost      │            │  │
│  │  └──────────────┘  └──────────────┘  └──────────────┘            │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                                                                          │
│  MESSAGE HISTORY                                                         │
│  ───────────────────────────────────────────────────────────────────    │
│                                                                          │
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │ 👤 Help me debug this React component...                          │  │
│  │    2:34 PM                                                         │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                                                                          │
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │ 🤖 I'll analyze the component. Let me read the file first...      │  │
│  │    2:34 PM  │  1,234 in / 567 out  │  $0.002                      │  │
│  │                                                                    │  │
│  │    📄 read_file: src/Component.tsx                                │  │
│  │    ✓ Completed in 45ms                                            │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                                                                          │
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │ 🤖 I found the issue. The useEffect dependency array...           │  │
│  │    2:35 PM  │  2,456 in / 1,234 out  │  $0.004                    │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Component Structure

```
SessionPanel
├── Header
│   ├── Title
│   └── Actions (Export, Clear)
│
├── SessionInfo
│   ├── ModelBadge
│   ├── ProviderBadge
│   ├── TimingInfo
│   └── TokenMetrics
│       ├── PromptCount
│       ├── CompletionCount
│       └── CostDisplay
│
└── MessageHistory
    └── MessageCard (repeated)
        ├── RoleIcon
        ├── ContentPreview
        ├── Timestamp
        ├── TokenUsage (assistant only)
        └── ToolCalls (if any)
            └── ToolCallItem
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.Session.SessionPanel where

import Prelude
import Data.Array (Array)
import Data.Maybe (Maybe)
import Data.DateTime (DateTime)

-- Session data
type Session =
  { id :: String
  , model :: String
  , provider :: String
  , startedAt :: DateTime
  , promptTokens :: Int
  , completionTokens :: Int
  , cost :: Number
  , messages :: Array Message
  }

-- Message with optional tool calls
type Message =
  { id :: String
  , role :: Role
  , content :: String
  , timestamp :: DateTime
  , usage :: Maybe MessageUsage
  , toolCalls :: Array ToolCall
  }

data Role = User | Assistant | System | Tool

type MessageUsage =
  { promptTokens :: Int
  , completionTokens :: Int
  , cost :: Number
  }

type ToolCall =
  { name :: String
  , status :: ToolStatus
  , durationMs :: Maybe Int
  }

data ToolStatus = Pending | Running | Completed | Failed

-- Component state
type State =
  { session :: Maybe Session
  , expandedMessages :: Set String  -- IDs of expanded messages
  , isExporting :: Boolean
  }

-- Actions
data Action
  = Receive (Maybe Session)
  | ToggleMessageExpand String
  | ExportSession
  | ClearSession
  | HandleExportResult (Either Error String)

-- Outputs
data Output
  = SessionCleared
  | SessionExported String
```

### Component

```purescript
component :: forall q m. MonadAff m => H.Component q (Maybe Session) Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      }
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state = case state.session of
  Nothing -> renderEmptyState
  Just session -> renderSession session state

renderEmptyState :: forall m. H.ComponentHTML Action () m
renderEmptyState =
  HH.div
    [ HP.class_ (H.ClassName "session-panel session-panel--empty") ]
    [ HH.div
        [ HP.class_ (H.ClassName "empty-state") ]
        [ HH.span [ HP.class_ (H.ClassName "empty-state__icon") ] [ HH.text "💬" ]
        , HH.p_ [ HH.text "No active session" ]
        , HH.p [ HP.class_ (H.ClassName "empty-state__hint") ] 
            [ HH.text "Start a conversation in OpenCode to see details here" ]
        ]
    ]

renderSession :: forall m. Session -> State -> H.ComponentHTML Action () m
renderSession session state =
  HH.div
    [ HP.class_ (H.ClassName "session-panel") ]
    [ -- Header with actions
      renderHeader state.isExporting
    
    -- Session info card
    , renderSessionInfo session
    
    -- Message history
    , HH.div
        [ HP.class_ (H.ClassName "session-panel__messages") ]
        [ HH.div [ HP.class_ (H.ClassName "section-title") ] [ HH.text "Message History" ]
        , HH.div
            [ HP.class_ (H.ClassName "message-list") ]
            (map (renderMessage state.expandedMessages) session.messages)
        ]
    ]

renderHeader :: forall m. Boolean -> H.ComponentHTML Action () m
renderHeader isExporting =
  HH.header
    [ HP.class_ (H.ClassName "session-panel__header") ]
    [ HH.h2_ [ HH.text "Session Details" ]
    , HH.div
        [ HP.class_ (H.ClassName "session-panel__actions") ]
        [ HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--secondary" ]
            , HP.disabled isExporting
            , HE.onClick \_ -> ExportSession
            ]
            [ HH.text $ if isExporting then "Exporting..." else "Export" ]
        , HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--ghost" ]
            , HE.onClick \_ -> ClearSession
            ]
            [ HH.text "Clear" ]
        ]
    ]

renderSessionInfo :: forall m. Session -> H.ComponentHTML Action () m
renderSessionInfo session =
  HH.div
    [ HP.class_ (H.ClassName "session-info") ]
    [ HH.div
        [ HP.class_ (H.ClassName "session-info__header") ]
        [ HH.span [ HP.class_ (H.ClassName "session-info__title") ] 
            [ HH.text "Current Session" ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "session-info__details") ]
        [ renderDetail "Model" session.model
        , renderDetail "Provider" session.provider
        , renderDetail "Started" (formatTime session.startedAt)
        , renderDetail "Duration" (formatDuration session.startedAt)
        ]
    , HH.div
        [ HP.class_ (H.ClassName "session-info__metrics") ]
        [ renderMetric (formatNumber session.promptTokens) "Prompt"
        , renderMetric (formatNumber session.completionTokens) "Completion"
        , renderMetric (formatUSD session.cost) "Cost"
        ]
    ]

renderMessage :: forall m. Set String -> Message -> H.ComponentHTML Action () m
renderMessage expandedIds message =
  let 
    isExpanded = Set.member message.id expandedIds
    roleIcon = case message.role of
      User -> "👤"
      Assistant -> "🤖"
      System -> "⚙️"
      Tool -> "🔧"
  in
    HH.div
      [ HP.classes $ messageClasses message.role
      , HE.onClick \_ -> ToggleMessageExpand message.id
      ]
      [ HH.div
          [ HP.class_ (H.ClassName "message__header") ]
          [ HH.span [ HP.class_ (H.ClassName "message__icon") ] [ HH.text roleIcon ]
          , HH.span [ HP.class_ (H.ClassName "message__content") ] 
              [ HH.text $ truncateContent isExpanded message.content ]
          ]
      , HH.div
          [ HP.class_ (H.ClassName "message__footer") ]
          [ HH.span [ HP.class_ (H.ClassName "message__time") ] 
              [ HH.text $ formatTime message.timestamp ]
          , case message.usage of
              Just usage -> renderMessageUsage usage
              Nothing -> HH.text ""
          ]
      , when (not $ null message.toolCalls) $
          HH.div
            [ HP.class_ (H.ClassName "message__tools") ]
            (map renderToolCall message.toolCalls)
      ]

renderToolCall :: forall m. ToolCall -> H.ComponentHTML Action () m
renderToolCall { name, status, durationMs } =
  HH.div
    [ HP.class_ (H.ClassName "tool-call") ]
    [ HH.span [ HP.class_ (H.ClassName "tool-call__icon") ] 
        [ HH.text $ statusIcon status ]
    , HH.span [ HP.class_ (H.ClassName "tool-call__name") ] 
        [ HH.text name ]
    , case durationMs of
        Just ms -> HH.span [ HP.class_ (H.ClassName "tool-call__duration") ] 
            [ HH.text $ show ms <> "ms" ]
        Nothing -> HH.text ""
    ]

statusIcon :: ToolStatus -> String
statusIcon = case _ of
  Pending -> "⏳"
  Running -> "🔄"
  Completed -> "✓"
  Failed -> "✗"

messageClasses :: Role -> Array H.ClassName
messageClasses role =
  [ H.ClassName "message" ] <> case role of
    User -> [ H.ClassName "message--user" ]
    Assistant -> [ H.ClassName "message--assistant" ]
    System -> [ H.ClassName "message--system" ]
    Tool -> [ H.ClassName "message--tool" ]
```

### Actions

```purescript
handleAction :: forall m. MonadAff m 
             => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive session ->
    H.modify_ _ { session = session }
  
  ToggleMessageExpand id ->
    H.modify_ \s -> s { expandedMessages = toggleSet id s.expandedMessages }
  
  ExportSession -> do
    H.modify_ _ { isExporting = true }
    session <- H.gets _.session
    result <- for session \s -> do
      -- Export to JSON/Markdown
      H.liftAff $ exportSessionToFile s
    H.modify_ _ { isExporting = false }
    for_ (join result) \path -> H.raise (SessionExported path)
  
  ClearSession -> do
    H.raise SessionCleared
  
  HandleExportResult result ->
    case result of
      Left error -> do
        -- Show error notification
        pure unit
      Right path -> do
        H.raise (SessionExported path)

toggleSet :: forall a. Ord a => a -> Set a -> Set a
toggleSet x set =
  if Set.member x set
  then Set.delete x set
  else Set.insert x set
```

---

## CSS Styling

```css
.session-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--color-bg-base);
}

.session-panel--empty {
  justify-content: center;
  align-items: center;
}

.session-panel__header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: var(--space-4);
  border-bottom: 1px solid var(--color-border-subtle);
}

.session-panel__header h2 {
  font-family: var(--font-mono);
  font-size: var(--font-size-lg);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-primary);
  margin: 0;
}

.session-panel__actions {
  display: flex;
  gap: var(--space-2);
}

.session-info {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: var(--card-border-radius);
  margin: var(--space-4);
  padding: var(--space-4);
}

.session-info__title {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-primary);
}

.session-info__details {
  display: grid;
  grid-template-columns: repeat(2, 1fr);
  gap: var(--space-2);
  margin: var(--space-3) 0;
}

.session-info__metrics {
  display: flex;
  justify-content: space-around;
  padding-top: var(--space-3);
  border-top: 1px solid var(--color-border-subtle);
}

.session-metric {
  text-align: center;
}

.session-metric__value {
  font-family: var(--font-mono);
  font-size: var(--font-size-xl);
  font-weight: var(--font-weight-bold);
  color: var(--color-text-primary);
  font-variant-numeric: tabular-nums;
}

.session-metric__label {
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
  text-transform: uppercase;
  letter-spacing: var(--letter-spacing-wider);
}

.session-panel__messages {
  flex: 1;
  overflow-y: auto;
  padding: 0 var(--space-4) var(--space-4);
}

.section-title {
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-secondary);
  text-transform: uppercase;
  letter-spacing: var(--letter-spacing-wider);
  margin-bottom: var(--space-3);
}

.message-list {
  display: flex;
  flex-direction: column;
  gap: var(--space-2);
}

.message {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  padding: var(--space-3);
  cursor: pointer;
  transition: border-color var(--transition-fast);
}

.message:hover {
  border-color: var(--color-border-default);
}

.message--user {
  border-left: 3px solid var(--color-primary);
}

.message--assistant {
  border-left: 3px solid var(--color-success);
}

.message__header {
  display: flex;
  gap: var(--space-2);
}

.message__icon {
  flex-shrink: 0;
}

.message__content {
  flex: 1;
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-text-primary);
  white-space: pre-wrap;
  overflow: hidden;
}

.message__footer {
  display: flex;
  justify-content: space-between;
  margin-top: var(--space-2);
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
}

.message__tools {
  margin-top: var(--space-2);
  padding-top: var(--space-2);
  border-top: 1px solid var(--color-border-subtle);
}

.tool-call {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  color: var(--color-text-secondary);
  padding: var(--space-1) 0;
}

.tool-call__name {
  color: var(--color-info);
}

.tool-call__duration {
  color: var(--color-text-tertiary);
}

.empty-state {
  text-align: center;
  color: var(--color-text-secondary);
}

.empty-state__icon {
  font-size: 48px;
  display: block;
  margin-bottom: var(--space-3);
}

.empty-state__hint {
  font-size: var(--font-size-sm);
  color: var(--color-text-tertiary);
}
```

---

## Export Formats

### JSON Export

```json
{
  "session": {
    "id": "sess_abc123",
    "model": "llama-3.3-70b",
    "provider": "venice",
    "startedAt": "2024-01-15T14:34:00Z",
    "totalTokens": 23955,
    "cost": 0.014
  },
  "messages": [
    {
      "role": "user",
      "content": "Help me debug this React component...",
      "timestamp": "2024-01-15T14:34:12Z"
    },
    {
      "role": "assistant",
      "content": "I'll analyze the component...",
      "timestamp": "2024-01-15T14:34:18Z",
      "usage": { "promptTokens": 1234, "completionTokens": 567 },
      "toolCalls": [
        { "name": "read_file", "args": "src/Component.tsx", "duration": 45 }
      ]
    }
  ]
}
```

### Markdown Export

```markdown
# Session Export

**Model:** llama-3.3-70b  
**Started:** Jan 15, 2024 2:34 PM  
**Tokens:** 23,955 (15,234 prompt / 8,721 completion)  
**Cost:** $0.014

---

## Conversation

### User (2:34 PM)
Help me debug this React component...

### Assistant (2:34 PM)
I'll analyze the component. Let me read the file first...

**Tool:** `read_file` → `src/Component.tsx` (45ms)

### Assistant (2:35 PM)  
I found the issue. The useEffect dependency array...
```

---

## Related Specifications

- `50-DASHBOARD-LAYOUT.md` - Parent view
- `23-SESSION-MANAGEMENT.md` - Session lifecycle
- `24-MESSAGE-FLOW.md` - Message handling

---

*"Every conversation tells a story. The session panel helps you read it."*
