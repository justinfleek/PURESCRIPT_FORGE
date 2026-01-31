# 58-FILE-CONTEXT-VIEW: AI Context Visibility

## Overview

The File Context View shows exactly what files the AI has read into its context window, their token costs, and lets users manage context to optimize token usage.

---

## The Problem

When working with AI, you have no idea:
- What files has the AI actually read?
- How many tokens is each file consuming?
- Is there duplicate/stale context?
- What files SHOULD be in context but aren't?

---

## Visual Design

### Full File Context View

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  FILE CONTEXT                                          [Refresh] [Clear All]│
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Context Budget: ████████████████████░░░░░░░░░░░░  67% (54,231 / 80,000 tk)│
│                                                                             │
│  ┌─ ACTIVE CONTEXT (12 files, 54,231 tokens) ────────────────────────────┐ │
│  │                                                                        │ │
│  │  ┌─ src/auth/ ─────────────────────────────── 3 files, 2,360 tk ───┐  │ │
│  │  │  [✓] 📄 session.ts        1,234 tk   Read 12:30    [−] [👁]     │  │ │
│  │  │  [✓] 📄 middleware.ts       892 tk   Read 12:30    [−] [👁]     │  │ │
│  │  │  [✓] 📄 types.ts            234 tk   Read 12:31    [−] [👁]     │  │ │
│  │  └─────────────────────────────────────────────────────────────────┘  │ │
│  │                                                                        │ │
│  │  ┌─ src/components/ ───────────────────────── 2 files, 988 tk ─────┐  │ │
│  │  │  [✓] 📄 Auth.tsx            567 tk   Read 12:32    [−] [👁]     │  │ │
│  │  │  [✓] 📝 Auth.test.tsx       421 tk   Written 12:33 [−] [👁]     │  │ │
│  │  └─────────────────────────────────────────────────────────────────┘  │ │
│  │                                                                        │ │
│  │  ┌─ src/api/ ──────────────────────────────── 4 files, 3,456 tk ───┐  │ │
│  │  │  [✓] 📄 routes.ts         1,456 tk   Read 12:35    [−] [👁]     │  │ │
│  │  │  [✓] 📄 handlers.ts       1,200 tk   Read 12:35    [−] [👁]     │  │ │
│  │  │  [✓] 📄 validation.ts       500 tk   Read 12:36    [−] [👁]     │  │ │
│  │  │  [✓] 📄 errors.ts           300 tk   Read 12:36    [−] [👁]     │  │ │
│  │  └─────────────────────────────────────────────────────────────────┘  │ │
│  │                                                                        │ │
│  │  [Select All] [Deselect All] [Remove Selected] [Collapse All]         │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ AI RECOMMENDATIONS ──────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  Based on your current session, consider adding:                      │ │
│  │                                                                        │ │
│  │  ⚡ src/api/auth/login.ts     ~800 tk   Referenced in routes.ts       │ │
│  │     [+ Add to Context]                                                │ │
│  │                                                                        │ │
│  │  ⚡ src/config/auth.ts        ~400 tk   Contains auth configuration   │ │
│  │     [+ Add to Context]                                                │ │
│  │                                                                        │ │
│  │  Consider removing (stale):                                           │ │
│  │                                                                        │ │
│  │  ⚠ src/utils/deprecated.ts   1,200 tk   Not referenced in 15 min     │ │
│  │     [Remove from Context]                                             │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ QUICK ACTIONS ───────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  [+ Add Files...]  [📁 Add Directory...]  [💾 Save as Preset...]     │ │
│  │                                                                        │ │
│  │  Presets: [Auth Module ▼] [API Layer ▼] [Full Stack ▼] [Custom...]   │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────────────┘
```

### File Preview Modal

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  FILE PREVIEW: src/auth/session.ts                                    [✕]  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Status: In Context    Tokens: 1,234    Last Read: 12:30 PM                │
│  Size: 3.2 KB          Lines: 89        Language: TypeScript               │
│                                                                             │
│  ┌─ CONTENT ─────────────────────────────────────────────────────────────┐ │
│  │   1 │ import { Token, Session } from './types';                       │ │
│  │   2 │ import { config } from '../config';                             │ │
│  │   3 │                                                                  │ │
│  │   4 │ export interface SessionManager {                               │ │
│  │   5 │   create(userId: string): Promise<Session>;                     │ │
│  │   6 │   validate(token: Token): Promise<boolean>;                     │ │
│  │   7 │   refresh(session: Session): Promise<Session>;                  │ │
│  │   8 │   destroy(sessionId: string): Promise<void>;                    │ │
│  │   9 │ }                                                                │ │
│  │  10 │                                                                  │ │
│  │  ...                                                                   │ │
│  │  42 │ export function isTokenValid(token: Token): boolean {           │ │
│  │  43 │   return expiry.getTime() > Date.now();  // Fixed UTC bug       │ │
│  │  44 │ }                                                                │ │
│  │                                                        [Show Full File] │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ AI INTERACTIONS ─────────────────────────────────────────────────────┐ │
│  │  • Read at 12:30 PM during "Debug Auth" session                       │ │
│  │  • Referenced 3 times in conversation                                 │ │
│  │  • AI suggested fix for line 43 (accepted)                            │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  [Remove from Context]  [Open in Editor]  [Copy Path]                      │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Data Model

### Context Entry

```typescript
interface ContextEntry {
  id: string;
  path: string;
  relativePath: string;
  
  // Token tracking
  tokens: number;
  estimatedTokens: number;  // Before actual count
  
  // Timing
  addedAt: Date;
  lastReadAt: Date;
  lastReferencedAt: Date;  // Last time AI mentioned this file
  
  // State
  status: 'reading' | 'in-context' | 'stale' | 'modified';
  isModifiedSinceRead: boolean;
  
  // Metadata
  language: string;
  sizeBytes: number;
  lineCount: number;
  
  // How it got into context
  source: 'user-added' | 'ai-read' | 'ai-written' | 'preset';
}

interface ContextState {
  entries: ContextEntry[];
  totalTokens: number;
  maxTokens: number;  // Model's context limit
  
  // Grouped view
  byDirectory: Map<string, ContextEntry[]>;
  
  // Recommendations
  suggestedAdditions: SuggestedFile[];
  suggestedRemovals: ContextEntry[];
}

interface SuggestedFile {
  path: string;
  reason: string;
  estimatedTokens: number;
  confidence: number;  // 0-1
  referencedBy: string[];  // Files that reference this one
}
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.Context.FileContextView where

import Prelude
import Data.Map (Map)
import Data.Set (Set)
import Data.DateTime (DateTime)

type ContextEntry =
  { id :: String
  , path :: String
  , relativePath :: String
  , tokens :: Int
  , addedAt :: DateTime
  , lastReadAt :: DateTime
  , status :: EntryStatus
  , language :: String
  , sizeBytes :: Int
  , source :: EntrySource
  }

data EntryStatus = Reading | InContext | Stale | Modified

data EntrySource = UserAdded | AIRead | AIWritten | Preset

type State =
  { entries :: Array ContextEntry
  , selectedIds :: Set String
  , expandedDirs :: Set String
  , totalTokens :: Int
  , maxTokens :: Int
  , suggestions :: Suggestions
  , previewFile :: Maybe ContextEntry
  , isLoading :: Boolean
  }

type Suggestions =
  { additions :: Array SuggestedFile
  , removals :: Array ContextEntry
  }

data Action
  = Initialize
  | Receive ContextState
  | ToggleSelect String
  | SelectAll
  | DeselectAll
  | ToggleDirectory String
  | RemoveSelected
  | RemoveEntry String
  | AddFiles (Array String)
  | AddDirectory String
  | AddSuggested String
  | PreviewFile ContextEntry
  | ClosePreview
  | SavePreset String
  | LoadPreset String
  | RefreshContext
  | ClearAll
```

### Component

```purescript
component :: forall q o m. MonadAff m => H.Component q ContextState o m
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
    [ HP.class_ (H.ClassName "file-context-view") ]
    [ -- Header with budget bar
      renderHeader state
    
    -- Active context grouped by directory
    , renderContextList state
    
    -- AI recommendations
    , renderRecommendations state.suggestions
    
    -- Quick actions
    , renderQuickActions
    
    -- Preview modal
    , case state.previewFile of
        Just entry -> renderPreviewModal entry
        Nothing -> HH.text ""
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.div
    [ HP.class_ (H.ClassName "context-header") ]
    [ HH.div
        [ HP.class_ (H.ClassName "context-header__title") ]
        [ HH.text "File Context" ]
    , HH.div
        [ HP.class_ (H.ClassName "context-header__actions") ]
        [ HH.button
            [ HP.class_ (H.ClassName "btn btn--secondary")
            , HE.onClick \_ -> RefreshContext
            ]
            [ HH.text "Refresh" ]
        , HH.button
            [ HP.class_ (H.ClassName "btn btn--ghost")
            , HE.onClick \_ -> ClearAll
            ]
            [ HH.text "Clear All" ]
        ]
    , renderTokenBudget state.totalTokens state.maxTokens
    ]

renderTokenBudget :: forall m. Int -> Int -> H.ComponentHTML Action () m
renderTokenBudget used max =
  let 
    percent = (toNumber used / toNumber max) * 100.0
    status = if percent > 90.0 then "critical"
             else if percent > 75.0 then "warning"
             else "normal"
  in
    HH.div
      [ HP.class_ (H.ClassName "token-budget") ]
      [ HH.div
          [ HP.class_ (H.ClassName "token-budget__label") ]
          [ HH.text "Context Budget:" ]
      , HH.div
          [ HP.classes [ H.ClassName "token-budget__bar", H.ClassName ("token-budget--" <> status) ] ]
          [ HH.div
              [ HP.class_ (H.ClassName "token-budget__fill")
              , HP.style $ "width: " <> show percent <> "%"
              ]
              []
          ]
      , HH.div
          [ HP.class_ (H.ClassName "token-budget__value") ]
          [ HH.text $ show (percent # round) <> "% (" <> 
                      formatNumber used <> " / " <> formatNumber max <> " tk)" ]
      ]

renderContextList :: forall m. State -> H.ComponentHTML Action () m
renderContextList state =
  let grouped = groupByDirectory state.entries
  in
    HH.div
      [ HP.class_ (H.ClassName "context-list") ]
      [ HH.div
          [ HP.class_ (H.ClassName "context-list__header") ]
          [ HH.text $ "Active Context (" <> show (length state.entries) <> 
                      " files, " <> formatNumber state.totalTokens <> " tokens)" ]
      , HH.div
          [ HP.class_ (H.ClassName "context-list__content") ]
          (map (renderDirectoryGroup state) (Map.toUnfoldable grouped))
      , renderBulkActions state
      ]

renderDirectoryGroup :: forall m. State -> Tuple String (Array ContextEntry) -> H.ComponentHTML Action () m
renderDirectoryGroup state (Tuple dir entries) =
  let 
    isExpanded = Set.member dir state.expandedDirs
    totalTokens = sum $ map _.tokens entries
  in
    HH.div
      [ HP.class_ (H.ClassName "directory-group") ]
      [ HH.div
          [ HP.class_ (H.ClassName "directory-group__header")
          , HE.onClick \_ -> ToggleDirectory dir
          ]
          [ HH.span [ HP.class_ (H.ClassName "directory-group__icon") ]
              [ HH.text $ if isExpanded then "▼" else "▶" ]
          , HH.span [ HP.class_ (H.ClassName "directory-group__name") ]
              [ HH.text dir ]
          , HH.span [ HP.class_ (H.ClassName "directory-group__stats") ]
              [ HH.text $ show (length entries) <> " files, " <> formatNumber totalTokens <> " tk" ]
          ]
      , when isExpanded $
          HH.div
            [ HP.class_ (H.ClassName "directory-group__entries") ]
            (map (renderEntry state.selectedIds) entries)
      ]

renderEntry :: forall m. Set String -> ContextEntry -> H.ComponentHTML Action () m
renderEntry selectedIds entry =
  let 
    isSelected = Set.member entry.id selectedIds
    icon = case entry.source of
      AIWritten -> "📝"
      _ -> "📄"
  in
    HH.div
      [ HP.classes $ entryClasses entry isSelected ]
      [ HH.input
          [ HP.type_ HP.InputCheckbox
          , HP.checked isSelected
          , HE.onClick \_ -> ToggleSelect entry.id
          ]
      , HH.span [ HP.class_ (H.ClassName "entry__icon") ] [ HH.text icon ]
      , HH.span [ HP.class_ (H.ClassName "entry__name") ] [ HH.text $ fileName entry.path ]
      , HH.span [ HP.class_ (H.ClassName "entry__tokens") ] [ HH.text $ formatNumber entry.tokens <> " tk" ]
      , HH.span [ HP.class_ (H.ClassName "entry__time") ] [ HH.text $ formatRelativeTime entry.lastReadAt ]
      , HH.div
          [ HP.class_ (H.ClassName "entry__actions") ]
          [ HH.button
              [ HP.class_ (H.ClassName "entry__action")
              , HE.onClick \_ -> RemoveEntry entry.id
              , HP.title "Remove from context"
              ]
              [ HH.text "−" ]
          , HH.button
              [ HP.class_ (H.ClassName "entry__action")
              , HE.onClick \_ -> PreviewFile entry
              , HP.title "Preview file"
              ]
              [ HH.text "👁" ]
          ]
      ]
```

---

## Context Tracking

### Bridge-Side Tracking

```typescript
// bridge/src/context/tracker.ts

export class ContextTracker {
  private entries: Map<string, ContextEntry> = new Map();
  private store: StateStore;
  
  constructor(store: StateStore) {
    this.store = store;
  }
  
  // Called when AI reads a file
  onFileRead(event: FileReadEvent): void {
    const entry = this.entries.get(event.path);
    
    if (entry) {
      // Update existing entry
      entry.lastReadAt = new Date();
      entry.status = 'in-context';
    } else {
      // Create new entry
      this.entries.set(event.path, {
        id: generateId(),
        path: event.path,
        relativePath: path.relative(process.cwd(), event.path),
        tokens: this.countTokens(event.content),
        addedAt: new Date(),
        lastReadAt: new Date(),
        lastReferencedAt: new Date(),
        status: 'in-context',
        isModifiedSinceRead: false,
        language: detectLanguage(event.path),
        sizeBytes: event.content.length,
        lineCount: event.content.split('\n').length,
        source: 'ai-read'
      });
    }
    
    this.broadcastUpdate();
  }
  
  // Called when AI writes a file
  onFileWritten(event: FileWriteEvent): void {
    const entry = this.entries.get(event.path);
    
    if (entry) {
      entry.lastReadAt = new Date();
      entry.tokens = this.countTokens(event.content);
      entry.source = 'ai-written';
    } else {
      // New file created by AI
      this.entries.set(event.path, {
        id: generateId(),
        path: event.path,
        relativePath: path.relative(process.cwd(), event.path),
        tokens: this.countTokens(event.content),
        addedAt: new Date(),
        lastReadAt: new Date(),
        lastReferencedAt: new Date(),
        status: 'in-context',
        isModifiedSinceRead: false,
        language: detectLanguage(event.path),
        sizeBytes: event.content.length,
        lineCount: event.content.split('\n').length,
        source: 'ai-written'
      });
    }
    
    this.broadcastUpdate();
  }
  
  // Generate recommendations
  generateRecommendations(): Suggestions {
    const additions: SuggestedFile[] = [];
    const removals: ContextEntry[] = [];
    
    // Find stale files (not referenced in 15+ minutes)
    const staleThreshold = 15 * 60 * 1000;
    for (const entry of this.entries.values()) {
      if (Date.now() - entry.lastReferencedAt.getTime() > staleThreshold) {
        removals.push(entry);
      }
    }
    
    // Find files that should be added (referenced by files in context)
    const imports = this.analyzeImports();
    for (const [file, referencedBy] of imports) {
      if (!this.entries.has(file)) {
        additions.push({
          path: file,
          reason: `Referenced in ${referencedBy[0]}`,
          estimatedTokens: this.estimateTokens(file),
          confidence: referencedBy.length / this.entries.size,
          referencedBy
        });
      }
    }
    
    return { additions, removals };
  }
  
  private broadcastUpdate(): void {
    this.store.updateContext({
      entries: Array.from(this.entries.values()),
      totalTokens: this.calculateTotalTokens(),
      suggestions: this.generateRecommendations()
    });
  }
}
```

---

## CSS Styling

```css
.file-context-view {
  display: flex;
  flex-direction: column;
  height: 100%;
  overflow: hidden;
}

.context-header {
  padding: var(--space-4);
  border-bottom: 1px solid var(--color-border-subtle);
}

.token-budget {
  display: flex;
  align-items: center;
  gap: var(--space-3);
  margin-top: var(--space-3);
}

.token-budget__bar {
  flex: 1;
  height: 8px;
  background: var(--color-bg-base);
  border-radius: 4px;
  overflow: hidden;
}

.token-budget__fill {
  height: 100%;
  background: var(--color-success);
  transition: width var(--transition-base);
}

.token-budget--warning .token-budget__fill {
  background: var(--color-warning);
}

.token-budget--critical .token-budget__fill {
  background: var(--color-error);
}

.context-list {
  flex: 1;
  overflow-y: auto;
  padding: var(--space-4);
}

.directory-group {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  margin-bottom: var(--space-2);
  overflow: hidden;
}

.directory-group__header {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  padding: var(--space-2) var(--space-3);
  cursor: pointer;
  background: var(--color-bg-elevated);
}

.directory-group__header:hover {
  background: var(--color-bg-hover);
}

.directory-group__name {
  flex: 1;
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-info);
}

.directory-group__stats {
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
}

.directory-group__entries {
  border-top: 1px solid var(--color-border-subtle);
}

.entry {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  padding: var(--space-2) var(--space-3);
  border-bottom: 1px solid var(--color-border-subtle);
}

.entry:last-child {
  border-bottom: none;
}

.entry:hover {
  background: var(--color-bg-hover);
}

.entry--stale {
  opacity: 0.6;
}

.entry__name {
  flex: 1;
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
}

.entry__tokens {
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  color: var(--color-text-secondary);
  font-variant-numeric: tabular-nums;
}

.entry__time {
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
}

.entry__actions {
  display: flex;
  gap: var(--space-1);
  opacity: 0;
  transition: opacity var(--transition-fast);
}

.entry:hover .entry__actions {
  opacity: 1;
}
```

---

## Related Specifications

- `24-MESSAGE-FLOW.md` - File read/write events
- `25-TOOL-EXECUTION.md` - Tool tracking
- `54-SESSION-PANEL.md` - Session view integration

---

*"Understanding what the AI knows is the first step to effective collaboration."*
