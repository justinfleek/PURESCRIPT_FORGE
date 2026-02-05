# 59-DIFF-VIEWER: AI Change Visualization

## Overview

The Diff Viewer shows exactly what changes the AI made to files, with inline explanations, accept/reject controls, and batch operations.

---

## The Problem

When AI modifies your code:
- What exactly changed?
- Why did it make that change?
- Can I accept some changes but not others?
- Can I see all pending changes at once?

---

## Visual Design

### Diff List View

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  CHANGES                                    [Accept All] [Reject All]       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Pending Changes: 4 files, 12 hunks                                        │
│                                                                             │
│  ┌─ src/auth/session.ts ─────────────────────── 2 changes ───────────────┐ │
│  │                                                                        │ │
│  │  12:33 PM • "Fix token expiration timezone bug"                       │ │
│  │                                                                        │ │
│  │  ┌─ Change 1/2 ─────────────────────────────────────────────────────┐ │ │
│  │  │   40   const now = new Date();                                    │ │ │
│  │  │   41   const expiry = new Date(token.expiresAt);                  │ │ │
│  │  │  -42   return expiry.getTime() > now.getTime();                   │ │ │
│  │  │  +42   return expiry.getTime() > Date.now(); // UTC timestamp     │ │ │
│  │  │   43 }                                                            │ │ │
│  │  │                                                                    │ │ │
│  │  │  💡 Uses Date.now() for consistent UTC comparison                 │ │ │
│  │  │                                          [Accept] [Reject] [Edit] │ │ │
│  │  └────────────────────────────────────────────────────────────────────┘ │ │
│  │                                                                        │ │
│  │  ┌─ Change 2/2 ─────────────────────────────────────────────────────┐ │ │
│  │  │  +15 │ // Token validation uses UTC timestamps exclusively        │ │ │
│  │  │  +16 │ // to avoid timezone-related session expiration bugs       │ │ │
│  │  │                                                                    │ │ │
│  │  │  💡 Added documentation comment explaining the fix                │ │ │
│  │  │                                          [Accept] [Reject] [Edit] │ │ │
│  │  └────────────────────────────────────────────────────────────────────┘ │ │
│  │                                                                        │ │
│  │  [Accept All in File] [Reject All in File] [View Full File]           │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ src/auth/session.test.ts ────────────────── NEW FILE ────────────────┐ │
│  │                                                                        │ │
│  │  12:34 PM • "Add tests for token validation"                          │ │
│  │                                                                        │ │
│  │  +1  │ import { isTokenValid } from './session';                      │ │
│  │  +2  │ import { describe, it, expect } from 'vitest';                 │ │
│  │  +3  │                                                                 │ │
│  │  +4  │ describe('isTokenValid', () => {                               │ │
│  │  +5  │   it('returns true for valid token', () => {                   │ │
│  │  ... │   (42 more lines)                              [Expand]        │ │
│  │                                                                        │ │
│  │  💡 New test file with 3 test cases for token validation             │ │
│  │                                          [Accept] [Reject] [Preview] │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Side-by-Side Diff View

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  DIFF: src/auth/session.ts                          [Unified] [Split]  [✕] │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ ORIGINAL ─────────────────────┐  ┌─ MODIFIED ─────────────────────┐   │
│  │                                 │  │                                 │   │
│  │  38 │ export function isToken  │  │  38 │ export function isToken  │   │
│  │  39 │   Valid(token: Token):   │  │  39 │   Valid(token: Token):   │   │
│  │  40 │   const now = new Date() │  │  40 │   const now = new Date() │   │
│  │  41 │   const expiry = new Dat │  │  41 │   const expiry = new Dat │   │
│  │  42 │   return expiry.getTime( │  │  42 │   return expiry.getTime( │   │
│  │     │ ) > now.getTime();       │  │     │ ) > Date.now();          │   │
│  │  43 │ }                        │  │  43 │ }                        │   │
│  │                                 │  │                                 │   │
│  └─────────────────────────────────┘  └─────────────────────────────────┘   │
│                                                                             │
│  ┌─ AI EXPLANATION ──────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  **Problem:** `new Date().getTime()` returns local time, but token    │ │
│  │  expiry is stored in UTC. This caused random logouts for users in     │ │
│  │  different timezones.                                                  │ │
│  │                                                                        │ │
│  │  **Solution:** `Date.now()` returns UTC milliseconds, ensuring        │ │
│  │  consistent comparison regardless of timezone.                         │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  [← Previous Change]  Change 1 of 2  [Next Change →]                       │
│                                                                             │
│  [Reject]  [Edit Before Accept]  [Accept]                                  │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Data Model

```typescript
interface FileDiff {
  id: string;
  path: string;
  status: 'modified' | 'created' | 'deleted' | 'renamed';
  
  // Timing
  timestamp: Date;
  messageId: string;  // Which AI message produced this
  
  // AI context
  description: string;  // AI's explanation
  reason: string;       // Why it made this change
  
  // Diff data
  hunks: DiffHunk[];
  
  // State
  reviewStatus: 'pending' | 'accepted' | 'rejected' | 'partial';
  
  // For renames
  oldPath?: string;
}

interface DiffHunk {
  id: string;
  startLine: number;
  endLine: number;
  
  // The actual diff
  lines: DiffLine[];
  
  // AI explanation for this specific hunk
  explanation?: string;
  
  // State
  status: 'pending' | 'accepted' | 'rejected';
}

interface DiffLine {
  type: 'context' | 'addition' | 'deletion';
  lineNumber: number;
  content: string;
}

interface DiffState {
  files: FileDiff[];
  selectedFileId: string | null;
  viewMode: 'list' | 'unified' | 'split';
  
  // Summary
  totalFiles: number;
  totalHunks: number;
  pendingCount: number;
  acceptedCount: number;
  rejectedCount: number;
}
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.Diff.DiffViewer where

import Prelude
import Data.Array (Array)
import Data.Maybe (Maybe)
import Data.DateTime (DateTime)

data FileStatus = Modified | Created | Deleted | Renamed

data ReviewStatus = Pending | Accepted | Rejected | Partial

data LineType = Context | Addition | Deletion

type DiffLine =
  { lineType :: LineType
  , lineNumber :: Int
  , content :: String
  }

type DiffHunk =
  { id :: String
  , startLine :: Int
  , endLine :: Int
  , lines :: Array DiffLine
  , explanation :: Maybe String
  , status :: ReviewStatus
  }

type FileDiff =
  { id :: String
  , path :: String
  , status :: FileStatus
  , timestamp :: DateTime
  , description :: String
  , reason :: String
  , hunks :: Array DiffHunk
  , reviewStatus :: ReviewStatus
  }

data ViewMode = ListView | UnifiedView | SplitView

type State =
  { files :: Array FileDiff
  , selectedFileId :: Maybe String
  , selectedHunkId :: Maybe String
  , viewMode :: ViewMode
  , isExpanded :: Map String Boolean
  }

data Action
  = Initialize
  | Receive (Array FileDiff)
  | SelectFile String
  | SelectHunk String
  | SetViewMode ViewMode
  | ToggleExpand String
  | AcceptHunk String
  | RejectHunk String
  | AcceptFile String
  | RejectFile String
  | AcceptAll
  | RejectAll
  | EditBeforeAccept String
  | ViewFullFile String
  | NavigatePrevious
  | NavigateNext

data Output
  = HunkAccepted String
  | HunkRejected String
  | FileAccepted String
  | FileRejected String
  | AllAccepted
  | AllRejected
```

### Diff Rendering

```purescript
renderDiffHunk :: forall m. DiffHunk -> H.ComponentHTML Action () m
renderDiffHunk hunk =
  HH.div
    [ HP.classes $ hunkClasses hunk.status ]
    [ HH.div
        [ HP.class_ (H.ClassName "hunk__lines") ]
        (map renderDiffLine hunk.lines)
    
    -- AI explanation
    , case hunk.explanation of
        Just exp ->
          HH.div
            [ HP.class_ (H.ClassName "hunk__explanation") ]
            [ HH.span [ HP.class_ (H.ClassName "explanation-icon") ] [ HH.text "💡" ]
            , HH.text exp
            ]
        Nothing -> HH.text ""
    
    -- Actions
    , HH.div
        [ HP.class_ (H.ClassName "hunk__actions") ]
        [ HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--success" ]
            , HE.onClick \_ -> AcceptHunk hunk.id
            ]
            [ HH.text "Accept" ]
        , HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--danger" ]
            , HE.onClick \_ -> RejectHunk hunk.id
            ]
            [ HH.text "Reject" ]
        , HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--secondary" ]
            , HE.onClick \_ -> EditBeforeAccept hunk.id
            ]
            [ HH.text "Edit" ]
        ]
    ]

renderDiffLine :: forall m. DiffLine -> H.ComponentHTML Action () m
renderDiffLine line =
  HH.div
    [ HP.classes $ lineClasses line.lineType ]
    [ HH.span
        [ HP.class_ (H.ClassName "line__prefix") ]
        [ HH.text $ linePrefix line.lineType ]
    , HH.span
        [ HP.class_ (H.ClassName "line__number") ]
        [ HH.text $ show line.lineNumber ]
    , HH.span
        [ HP.class_ (H.ClassName "line__content") ]
        [ HH.text line.content ]
    ]

linePrefix :: LineType -> String
linePrefix = case _ of
  Context -> " "
  Addition -> "+"
  Deletion -> "-"

lineClasses :: LineType -> Array H.ClassName
lineClasses lineType =
  [ H.ClassName "diff-line" ] <>
  case lineType of
    Context -> []
    Addition -> [ H.ClassName "diff-line--addition" ]
    Deletion -> [ H.ClassName "diff-line--deletion" ]
```

### Split View

```purescript
renderSplitView :: forall m. FileDiff -> H.ComponentHTML Action () m
renderSplitView file =
  let 
    { original, modified } = splitDiff file.hunks
  in
    HH.div
      [ HP.class_ (H.ClassName "split-view") ]
      [ HH.div
          [ HP.class_ (H.ClassName "split-view__pane split-view__original") ]
          [ HH.div [ HP.class_ (H.ClassName "pane-header") ] [ HH.text "ORIGINAL" ]
          , HH.div [ HP.class_ (H.ClassName "pane-content") ]
              (map renderOriginalLine original)
          ]
      , HH.div
          [ HP.class_ (H.ClassName "split-view__pane split-view__modified") ]
          [ HH.div [ HP.class_ (H.ClassName "pane-header") ] [ HH.text "MODIFIED" ]
          , HH.div [ HP.class_ (H.ClassName "pane-content") ]
              (map renderModifiedLine modified)
          ]
      ]
```

---

## CSS Styling

```css
.diff-viewer {
  display: flex;
  flex-direction: column;
  height: 100%;
}

.diff-list {
  flex: 1;
  overflow-y: auto;
  padding: var(--space-4);
}

.diff-file {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  margin-bottom: var(--space-3);
  overflow: hidden;
}

.diff-file__header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: var(--space-3);
  background: var(--color-bg-elevated);
  border-bottom: 1px solid var(--color-border-subtle);
}

.diff-file__path {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-info);
}

.diff-file__badge {
  padding: 2px 8px;
  border-radius: 4px;
  font-size: var(--font-size-xs);
  font-weight: var(--font-weight-semibold);
}

.diff-file__badge--new {
  background: var(--color-success-dim);
  color: var(--color-success);
}

.diff-file__badge--modified {
  background: var(--color-warning-dim);
  color: var(--color-warning);
}

.diff-file__badge--deleted {
  background: var(--color-error-dim);
  color: var(--color-error);
}

.hunk {
  border-bottom: 1px solid var(--color-border-subtle);
  padding: var(--space-3);
}

.hunk:last-child {
  border-bottom: none;
}

.hunk--accepted {
  background: rgba(34, 197, 94, 0.05);
  border-left: 3px solid var(--color-success);
}

.hunk--rejected {
  background: rgba(239, 68, 68, 0.05);
  border-left: 3px solid var(--color-error);
  opacity: 0.6;
}

.diff-line {
  display: flex;
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  line-height: 1.6;
}

.diff-line--addition {
  background: rgba(34, 197, 94, 0.15);
  color: var(--color-success);
}

.diff-line--deletion {
  background: rgba(239, 68, 68, 0.15);
  color: var(--color-error);
  text-decoration: line-through;
}

.line__prefix {
  width: 20px;
  text-align: center;
  user-select: none;
  color: var(--color-text-tertiary);
}

.line__number {
  width: 40px;
  text-align: right;
  padding-right: var(--space-2);
  color: var(--color-text-tertiary);
  user-select: none;
}

.line__content {
  flex: 1;
  white-space: pre;
  overflow-x: auto;
}

.hunk__explanation {
  display: flex;
  align-items: flex-start;
  gap: var(--space-2);
  margin-top: var(--space-2);
  padding: var(--space-2);
  background: var(--color-bg-base);
  border-radius: 4px;
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
}

.hunk__actions {
  display: flex;
  justify-content: flex-end;
  gap: var(--space-2);
  margin-top: var(--space-3);
  padding-top: var(--space-3);
  border-top: 1px solid var(--color-border-subtle);
}

/* Split view */
.split-view {
  display: flex;
  flex: 1;
  overflow: hidden;
}

.split-view__pane {
  flex: 1;
  display: flex;
  flex-direction: column;
  overflow: hidden;
}

.split-view__original {
  border-right: 1px solid var(--color-border-default);
}

.pane-header {
  padding: var(--space-2) var(--space-3);
  background: var(--color-bg-elevated);
  font-size: var(--font-size-xs);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-secondary);
  text-transform: uppercase;
  letter-spacing: var(--letter-spacing-wider);
}

.pane-content {
  flex: 1;
  overflow: auto;
  padding: var(--space-2);
}
```

---

## Integration with Tool Execution

```typescript
// Track file changes from AI tool use
openCodeClient.on('tool.execute.after', (event) => {
  if (event.tool === 'write_file') {
    const diff = generateDiff(event.args.path, event.result.content);
    
    diffStore.addFileDiff({
      id: generateId(),
      path: event.args.path,
      status: fs.existsSync(event.args.path) ? 'modified' : 'created',
      timestamp: new Date(),
      messageId: currentMessage.id,
      description: extractDescription(currentMessage),
      reason: extractReason(currentMessage),
      hunks: diff.hunks,
      reviewStatus: 'pending'
    });
    
    broadcastDiffUpdate();
  }
});
```

---

## Related Specifications

- `25-TOOL-EXECUTION.md` - Tool event tracking
- `58-FILE-CONTEXT-VIEW.md` - File context
- `54-SESSION-PANEL.md` - Session integration

---

*"Every AI change should be understood before it's accepted."*
