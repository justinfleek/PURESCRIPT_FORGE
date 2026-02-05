# 25-TOOL-EXECUTION: Tracking, Timing, and Visualization

## Overview

Tool execution tracking provides visibility into every file read, write, command execution, and MCP call made by the AI. It captures timing, results, and enables visualization in the session panel.

---

## Tool Categories

| Category | Tools | Tracking Level |
|----------|-------|----------------|
| File System | read_file, write_file, list_directory | Full content + timing |
| Commands | execute_command, run_tests | Output + exit code + timing |
| Search | search_files, grep | Results + matches + timing |
| MCP | Any MCP tool | Args + result + timing |

---

## Visual Design

### Inline Tool Display

```
┌─────────────────────────────────────────────────────────────────┐
│  🤖 Assistant                                                   │
│                                                                 │
│  I'll analyze the authentication code. Let me read the files.  │
│                                                                 │
│  ┌─ TOOL: read_file ─────────────────────────────────────────┐ │
│  │  📄 src/auth/session.ts                          45ms ✓   │ │
│  │  1,234 tokens                                    [Expand]  │ │
│  └───────────────────────────────────────────────────────────┘ │
│                                                                 │
│  ┌─ TOOL: read_file ─────────────────────────────────────────┐ │
│  │  📄 src/auth/middleware.ts                       32ms ✓   │ │
│  │  892 tokens                                      [Expand]  │ │
│  └───────────────────────────────────────────────────────────┘ │
│                                                                 │
│  Found the issue in session.ts line 42...                      │
└─────────────────────────────────────────────────────────────────┘
```

### Expanded Tool View

```
┌─────────────────────────────────────────────────────────────────┐
│  TOOL: read_file                                    [Collapse] │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Path: src/auth/session.ts                                     │
│  Status: ✓ Success                                             │
│  Duration: 45ms                                                │
│  Tokens: 1,234                                                 │
│                                                                 │
│  ┌─ FILE CONTENT (preview) ─────────────────────────────────┐ │
│  │   1 │ import { Token, Session } from './types';          │ │
│  │   2 │ import { config } from '../config';                │ │
│  │   3 │                                                     │ │
│  │   4 │ export interface SessionManager {                  │ │
│  │   5 │   create(userId: string): Promise<Session>;        │ │
│  │   6 │   validate(token: Token): Promise<boolean>;        │ │
│  │  ...│ (89 lines total)                    [View Full] │ │
│  └───────────────────────────────────────────────────────────┘ │
│                                                                 │
│  [Open in Editor]  [Copy Path]  [Add to Context]               │
└─────────────────────────────────────────────────────────────────┘
```

### Tool Running State

```
┌─────────────────────────────────────────────────────────────────┐
│  ┌─ TOOL: write_file ────────────────────────────────────────┐ │
│  │  📝 src/auth/session.ts                      ⏳ Running... │ │
│  │  ████████████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░     │ │
│  └───────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

### Tool Error State

```
┌─────────────────────────────────────────────────────────────────┐
│  ┌─ TOOL: execute_command ───────────────────────────────────┐ │
│  │  ⚠ npm run test                              234ms ✗      │ │
│  │  Exit code: 1                                             │ │
│  │                                                           │ │
│  │  ┌─ ERROR OUTPUT ──────────────────────────────────────┐ │ │
│  │  │  FAIL src/auth/session.test.ts                      │ │ │
│  │  │  ● Session validation › should reject expired token │ │ │
│  │  │    Expected: false                                   │ │ │
│  │  │    Received: true                                    │ │ │
│  │  └─────────────────────────────────────────────────────┘ │ │
│  │                                                           │ │
│  │  [Retry]  [View Full Output]  [Copy Error]               │ │
│  └───────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

---

## Data Model

```typescript
interface ToolCall {
  id: string;
  messageId: string;
  sessionId: string;
  
  // Tool info
  name: string;
  category: ToolCategory;
  args: Record<string, any>;
  
  // Result
  status: ToolStatus;
  result: any;
  error?: string;
  
  // Timing
  startedAt: Date;
  completedAt?: Date;
  durationMs?: number;
  
  // For file operations
  file?: {
    path: string;
    content?: string;
    tokens?: number;
    size?: number;
    language?: string;
  };
  
  // For commands
  command?: {
    cmd: string;
    exitCode?: number;
    stdout?: string;
    stderr?: string;
  };
}

type ToolCategory = 'filesystem' | 'command' | 'search' | 'mcp';

type ToolStatus = 'pending' | 'running' | 'completed' | 'error';

interface ToolExecutionEvent {
  type: 'tool.start' | 'tool.progress' | 'tool.complete' | 'tool.error';
  toolCall: ToolCall;
  progress?: number;  // 0-100
}
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.Tool where

import Prelude
import Data.Maybe (Maybe)

type ToolCall =
  { id :: String
  , name :: String
  , category :: ToolCategory
  , args :: Foreign
  , status :: ToolStatus
  , result :: Maybe Foreign
  , error :: Maybe String
  , startedAt :: DateTime
  , completedAt :: Maybe DateTime
  , durationMs :: Maybe Int
  , file :: Maybe FileInfo
  , command :: Maybe CommandInfo
  }

data ToolCategory
  = Filesystem
  | Command
  | Search
  | MCP

data ToolStatus
  = Pending
  | Running
  | Completed
  | Error

type FileInfo =
  { path :: String
  , content :: Maybe String
  , tokens :: Maybe Int
  , size :: Maybe Int
  , language :: Maybe String
  }

type CommandInfo =
  { cmd :: String
  , exitCode :: Maybe Int
  , stdout :: Maybe String
  , stderr :: Maybe String
  }

type State =
  { isExpanded :: Boolean
  , showFullContent :: Boolean
  }

data Action
  = ToggleExpand
  | ShowFullContent
  | HideFullContent
  | OpenInEditor
  | CopyPath
  | Retry
```

### Tool Card Component

```purescript
module Sidepanel.Components.Tool.ToolCard where

component :: forall q m. MonadAff m => H.Component q ToolCall Output m
component = H.mkComponent
  { initialState: const { isExpanded: false, showFullContent: false }
  , render
  , eval: H.mkEval $ H.defaultEval { handleAction = handleAction }
  }

render :: forall m. ToolCall -> State -> H.ComponentHTML Action () m
render tool state =
  HH.div
    [ HP.classes $ toolClasses tool.status ]
    [ -- Header (always visible)
      renderHeader tool
    
    -- Expanded content
    , when state.isExpanded $ renderExpanded tool state
    ]

renderHeader :: forall m. ToolCall -> H.ComponentHTML Action () m
renderHeader tool =
  HH.div
    [ HP.class_ (H.ClassName "tool-card__header")
    , HE.onClick \_ -> ToggleExpand
    ]
    [ -- Icon based on category
      HH.span [ HP.class_ (H.ClassName "tool-card__icon") ]
        [ HH.text $ categoryIcon tool.category ]
    
    -- Tool name and main arg
    , HH.span [ HP.class_ (H.ClassName "tool-card__name") ]
        [ HH.text tool.name ]
    
    -- Main argument (file path, command, etc)
    , HH.span [ HP.class_ (H.ClassName "tool-card__arg") ]
        [ HH.text $ mainArg tool ]
    
    -- Status indicator
    , renderStatus tool.status tool.durationMs
    
    -- Expand indicator
    , HH.span [ HP.class_ (H.ClassName "tool-card__expand") ]
        [ HH.text "▼" ]
    ]

renderStatus :: forall m. ToolStatus -> Maybe Int -> H.ComponentHTML Action () m
renderStatus status duration =
  HH.span
    [ HP.class_ (H.ClassName "tool-card__status") ]
    [ case status of
        Pending -> HH.text "⏳"
        Running -> HH.span [ HP.class_ (H.ClassName "spinning") ] [ HH.text "🔄" ]
        Completed -> HH.text $ "✓ " <> maybe "" (\d -> show d <> "ms") duration
        Error -> HH.text "✗"
    ]

renderExpanded :: forall m. ToolCall -> State -> H.ComponentHTML Action () m
renderExpanded tool state =
  HH.div
    [ HP.class_ (H.ClassName "tool-card__expanded") ]
    [ -- Metadata
      HH.div
        [ HP.class_ (H.ClassName "tool-card__meta") ]
        [ renderMeta "Path" (tool.file <#> _.path)
        , renderMeta "Status" (Just $ show tool.status)
        , renderMeta "Duration" (tool.durationMs <#> \d -> show d <> "ms")
        , renderMeta "Tokens" (tool.file >>= _.tokens <#> show)
        ]
    
    -- Content (for file operations)
    , case tool.file of
        Just file -> renderFileContent file state
        Nothing -> HH.text ""
    
    -- Output (for commands)
    , case tool.command of
        Just cmd -> renderCommandOutput cmd
        Nothing -> HH.text ""
    
    -- Error (if any)
    , case tool.error of
        Just err -> renderError err
        Nothing -> HH.text ""
    
    -- Actions
    , renderActions tool
    ]

renderFileContent :: forall m. FileInfo -> State -> H.ComponentHTML Action () m
renderFileContent file state =
  case file.content of
    Nothing -> HH.text ""
    Just content ->
      HH.div
        [ HP.class_ (H.ClassName "tool-card__content") ]
        [ HH.pre
            [ HP.class_ (H.ClassName "code-preview") ]
            [ HH.code_
                [ HH.text $ if state.showFullContent
                    then content
                    else truncateContent content 10
                ]
            ]
        , unless state.showFullContent $
            HH.button
              [ HP.class_ (H.ClassName "btn btn--link")
              , HE.onClick \_ -> ShowFullContent
              ]
              [ HH.text "View Full" ]
        ]

renderCommandOutput :: forall m. CommandInfo -> H.ComponentHTML Action () m
renderCommandOutput cmd =
  HH.div
    [ HP.class_ (H.ClassName "tool-card__output") ]
    [ case cmd.exitCode of
        Just code | code /= 0 ->
          HH.div [ HP.class_ (H.ClassName "exit-code exit-code--error") ]
            [ HH.text $ "Exit code: " <> show code ]
        _ -> HH.text ""
    
    , case cmd.stderr of
        Just stderr | stderr /= "" ->
          HH.div [ HP.class_ (H.ClassName "stderr") ]
            [ HH.pre_ [ HH.text stderr ] ]
        _ -> HH.text ""
    
    , case cmd.stdout of
        Just stdout | stdout /= "" ->
          HH.div [ HP.class_ (H.ClassName "stdout") ]
            [ HH.pre_ [ HH.text stdout ] ]
        _ -> HH.text ""
    ]

renderActions :: forall m. ToolCall -> H.ComponentHTML Action () m
renderActions tool =
  HH.div
    [ HP.class_ (H.ClassName "tool-card__actions") ]
    [ when (tool.category == Filesystem && isJust tool.file) $
        HH.button
          [ HP.class_ (H.ClassName "btn btn--secondary btn--sm")
          , HE.onClick \_ -> OpenInEditor
          ]
          [ HH.text "Open in Editor" ]
    
    , when (isJust tool.file) $
        HH.button
          [ HP.class_ (H.ClassName "btn btn--ghost btn--sm")
          , HE.onClick \_ -> CopyPath
          ]
          [ HH.text "Copy Path" ]
    
    , when (tool.status == Error) $
        HH.button
          [ HP.class_ (H.ClassName "btn btn--warning btn--sm")
          , HE.onClick \_ -> Retry
          ]
          [ HH.text "Retry" ]
    ]

categoryIcon :: ToolCategory -> String
categoryIcon = case _ of
  Filesystem -> "📄"
  Command -> "⚡"
  Search -> "🔍"
  MCP -> "🔌"

mainArg :: ToolCall -> String
mainArg tool = case tool.name of
  "read_file" -> fromMaybe "" (tool.file <#> _.path)
  "write_file" -> fromMaybe "" (tool.file <#> _.path)
  "execute_command" -> fromMaybe "" (tool.command <#> _.cmd)
  "list_directory" -> fromMaybe "" (Foreign.lookup "path" tool.args)
  "search_files" -> fromMaybe "" (Foreign.lookup "query" tool.args)
  _ -> ""
```

---

## Bridge Event Handling

```typescript
// bridge/src/tools/tracker.ts

export class ToolTracker {
  private activeCalls: Map<string, ToolCall> = new Map();
  private store: StateStore;
  private db: Database;
  
  constructor(store: StateStore, db: Database) {
    this.store = store;
    this.db = db;
  }
  
  onToolStart(event: ToolExecuteBeforeEvent): void {
    const toolCall: ToolCall = {
      id: generateId(),
      messageId: event.messageId,
      sessionId: event.sessionId,
      name: event.tool,
      category: this.categorize(event.tool),
      args: event.args,
      status: 'running',
      result: null,
      startedAt: new Date()
    };
    
    // Track file info if applicable
    if (event.tool === 'read_file' || event.tool === 'write_file') {
      toolCall.file = {
        path: event.args.path,
        language: detectLanguage(event.args.path)
      };
    }
    
    // Track command info
    if (event.tool === 'execute_command') {
      toolCall.command = {
        cmd: event.args.command
      };
    }
    
    this.activeCalls.set(toolCall.id, toolCall);
    
    // Broadcast to browser
    this.store.broadcast({
      method: 'tool.start',
      params: toolCall
    });
  }
  
  onToolComplete(event: ToolExecuteAfterEvent): void {
    const toolCall = this.findActiveCall(event);
    if (!toolCall) return;
    
    toolCall.status = event.error ? 'error' : 'completed';
    toolCall.result = event.result;
    toolCall.error = event.error?.message;
    toolCall.completedAt = new Date();
    toolCall.durationMs = toolCall.completedAt.getTime() - toolCall.startedAt.getTime();
    
    // Enrich file info
    if (toolCall.file) {
      if (event.tool === 'read_file' && event.result) {
        toolCall.file.content = event.result;
        toolCall.file.tokens = this.countTokens(event.result);
        toolCall.file.size = event.result.length;
      } else if (event.tool === 'write_file' && event.args.content) {
        toolCall.file.content = event.args.content;
        toolCall.file.tokens = this.countTokens(event.args.content);
        toolCall.file.size = event.args.content.length;
      }
    }
    
    // Enrich command info
    if (toolCall.command && event.result) {
      toolCall.command.exitCode = event.result.exitCode;
      toolCall.command.stdout = event.result.stdout;
      toolCall.command.stderr = event.result.stderr;
    }
    
    // Save to database
    this.db.insertToolCall(toolCall);
    
    // Broadcast to browser
    this.store.broadcast({
      method: 'tool.complete',
      params: toolCall
    });
    
    this.activeCalls.delete(toolCall.id);
  }
  
  private categorize(tool: string): ToolCategory {
    const filesystem = ['read_file', 'write_file', 'list_directory', 'delete_file'];
    const command = ['execute_command', 'run_tests'];
    const search = ['search_files', 'grep'];
    
    if (filesystem.includes(tool)) return 'filesystem';
    if (command.includes(tool)) return 'command';
    if (search.includes(tool)) return 'search';
    return 'mcp';
  }
}
```

---

## CSS Styling

```css
.tool-card {
  border: 1px solid var(--color-border-subtle);
  border-radius: 6px;
  margin: var(--space-2) 0;
  overflow: hidden;
  transition: all var(--transition-fast);
}

.tool-card--completed {
  border-left: 3px solid var(--color-success);
}

.tool-card--error {
  border-left: 3px solid var(--color-error);
}

.tool-card--running {
  border-left: 3px solid var(--color-info);
}

.tool-card__header {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  padding: var(--space-2) var(--space-3);
  background: var(--color-bg-elevated);
  cursor: pointer;
}

.tool-card__header:hover {
  background: var(--color-bg-hover);
}

.tool-card__icon {
  font-size: 14px;
}

.tool-card__name {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  font-weight: var(--font-weight-medium);
  color: var(--color-info);
}

.tool-card__arg {
  flex: 1;
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.tool-card__status {
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
}

.tool-card__expanded {
  padding: var(--space-3);
  border-top: 1px solid var(--color-border-subtle);
  background: var(--color-bg-surface);
}

.tool-card__meta {
  display: grid;
  grid-template-columns: repeat(2, 1fr);
  gap: var(--space-2);
  margin-bottom: var(--space-3);
}

.code-preview {
  max-height: 200px;
  overflow: auto;
  background: var(--color-bg-base);
  border-radius: 4px;
  padding: var(--space-2);
  font-size: var(--font-size-sm);
}

.stderr {
  background: var(--color-error-dim);
  color: var(--color-error);
  padding: var(--space-2);
  border-radius: 4px;
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
}

.exit-code--error {
  color: var(--color-error);
  font-weight: var(--font-weight-semibold);
}

.spinning {
  animation: spin 1s linear infinite;
}

@keyframes spin {
  from { transform: rotate(0deg); }
  to { transform: rotate(360deg); }
}
```

---

## Related Specifications

- `24-MESSAGE-FLOW.md` - Message lifecycle
- `54-SESSION-PANEL.md` - Session view
- `67-PERFORMANCE-PROFILER.md` - Timing analysis

---

*"Every tool call tells a story. Make it readable."*
