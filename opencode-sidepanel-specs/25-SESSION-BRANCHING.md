# 25-SESSION-BRANCHING: Conversation Forking and Comparison

## Overview

Session Branching allows users to fork a conversation at any point to explore different approaches, compare outcomes, and merge successful branches back. Think of it as "git for AI conversations."

---

## Use Cases

1. **Exploration** - "What if I asked differently?"
2. **A/B Testing** - Compare two AI approaches to the same problem
3. **Safe Experimentation** - Try risky changes without losing working state
4. **Learning** - See how different prompts lead to different outcomes

---

## Visual Design

### Branch Indicator in Session

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  SESSION: Debug Auth                                        🌿 main [+2]    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ BRANCH SELECTOR ─────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  🌿 main (current)           12 messages    23,955 tk                 │ │
│  │  └─ 🌿 try-hooks             +5 messages    +8,234 tk    [Switch]     │ │
│  │  └─ 🌿 class-approach        +3 messages    +4,521 tk    [Switch]     │ │
│  │                                                                        │ │
│  │  [+ New Branch from Here]  [Compare Branches]  [Merge Branch]         │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
```

### Branch Creation Modal

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  CREATE BRANCH                                                        [✕]  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Branch from: Message #8 "Can you fix it and write a test?"                │
│                                                                             │
│  ┌─ BRANCH NAME ─────────────────────────────────────────────────────────┐ │
│  │  try-hooks-approach                                                    │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ DESCRIPTION (optional) ──────────────────────────────────────────────┐ │
│  │  Try refactoring to React hooks instead of class component            │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ WHAT TO INCLUDE ─────────────────────────────────────────────────────┐ │
│  │  [✓] All messages up to branch point                                  │ │
│  │  [✓] File context                                                      │ │
│  │  [✓] Balance at branch point: 45.2 Diem                               │ │
│  │  [ ] Include pending changes                                           │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│                                              [Cancel]  [Create Branch]     │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Branch Comparison View

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  COMPARE BRANCHES                                                     [✕]  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ COMPARISON ──────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  🌿 main                          vs          🌿 try-hooks            │ │
│  │                                                                        │ │
│  │  ┌─────────────────────────┐      ┌─────────────────────────┐        │ │
│  │  │ Messages: 12            │      │ Messages: 17 (+5)       │        │ │
│  │  │ Tokens: 23,955          │      │ Tokens: 32,189 (+8,234) │        │ │
│  │  │ Cost: $0.014            │      │ Cost: $0.019 (+$0.005)  │        │ │
│  │  │ Files changed: 2        │      │ Files changed: 3        │        │ │
│  │  └─────────────────────────┘      └─────────────────────────┘        │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ DIVERGENCE POINT ────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  Message #8: "Can you fix it and write a test?"                       │ │
│  │                                                                        │ │
│  │  ┌─ main response ──────────┐  ┌─ try-hooks response ───────────┐    │ │
│  │  │ "I'll fix the class      │  │ "Let me refactor this to use   │    │ │
│  │  │ component by updating    │  │ React hooks instead, which     │    │ │
│  │  │ the lifecycle method..." │  │ will make it cleaner..."       │    │ │
│  │  └──────────────────────────┘  └─────────────────────────────────┘    │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ FILE CHANGES COMPARISON ─────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  📄 Auth.tsx                                                          │ │
│  │     main: Class component with setState                               │ │
│  │     try-hooks: Functional component with useState/useEffect           │ │
│  │     [View Diff]                                                       │ │
│  │                                                                        │ │
│  │  📄 Auth.test.tsx                                                     │ │
│  │     main: Tests lifecycle methods                                     │ │
│  │     try-hooks: Tests hook behavior                                    │ │
│  │     [View Diff]                                                       │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  [Switch to main]  [Switch to try-hooks]  [Merge try-hooks → main]        │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Data Model

```typescript
interface Session {
  id: string;
  title: string;
  
  // Branch info
  branchName: string;          // 'main' for root
  parentSessionId?: string;    // undefined for root
  branchPoint?: number;        // Message index where branched
  
  // Branch metadata
  createdAt: Date;
  description?: string;
  
  // Messages and state
  messages: Message[];
  
  // Metrics
  promptTokens: number;
  completionTokens: number;
  cost: number;
}

interface SessionTree {
  rootSessionId: string;
  branches: Map<string, Session>;
  
  // Quick lookups
  branchNames: Map<string, string>;  // branchName -> sessionId
  childBranches: Map<string, string[]>;  // sessionId -> child sessionIds
}

interface BranchComparison {
  baseSession: Session;
  compareSession: Session;
  
  divergencePoint: number;  // Message index
  
  metrics: {
    messageDiff: number;
    tokenDiff: number;
    costDiff: number;
    filesDiff: string[];
  };
  
  fileDiffs: Map<string, FileDiff>;
}

interface MergeRequest {
  sourceSessionId: string;
  targetSessionId: string;
  
  // What to merge
  includeMessages: boolean;
  includeFileChanges: boolean;
  
  // Conflict resolution
  conflictStrategy: 'source' | 'target' | 'manual';
}
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Session.Branching where

import Prelude
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.Array (Array)

type SessionBranch =
  { id :: String
  , name :: String
  , parentId :: Maybe String
  , branchPoint :: Maybe Int
  , description :: Maybe String
  , messageCount :: Int
  , tokenCount :: Int
  , cost :: Number
  , createdAt :: DateTime
  }

type SessionTree =
  { rootId :: String
  , branches :: Map String SessionBranch
  , currentBranchId :: String
  }

data BranchAction
  = CreateBranch { name :: String, description :: Maybe String, fromMessage :: Int }
  | SwitchBranch String
  | DeleteBranch String
  | RenameBranch String String
  | CompareBranches String String
  | MergeBranch { source :: String, target :: String }

type BranchState =
  { tree :: Maybe SessionTree
  , showBranchSelector :: Boolean
  , showComparison :: Maybe BranchComparison
  , showCreateModal :: Boolean
  , pendingMerge :: Maybe MergeRequest
  }
```

### Branch Selector Component

```purescript
module Sidepanel.Components.BranchSelector where

renderBranchSelector :: forall m. SessionTree -> H.ComponentHTML BranchAction () m
renderBranchSelector tree =
  HH.div
    [ HP.class_ (H.ClassName "branch-selector") ]
    [ HH.div
        [ HP.class_ (H.ClassName "branch-selector__header") ]
        [ HH.span [ HP.class_ (H.ClassName "branch-icon") ] [ HH.text "🌿" ]
        , HH.span [ HP.class_ (H.ClassName "branch-name") ] 
            [ HH.text $ getCurrentBranchName tree ]
        , HH.span [ HP.class_ (H.ClassName "branch-count") ]
            [ HH.text $ "[+" <> show (Map.size tree.branches - 1) <> "]" ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "branch-selector__list") ]
        [ renderBranchTree tree.rootId tree 0 ]
    , HH.div
        [ HP.class_ (H.ClassName "branch-selector__actions") ]
        [ HH.button
            [ HP.class_ (H.ClassName "btn btn--primary")
            , HE.onClick \_ -> ShowCreateModal
            ]
            [ HH.text "+ New Branch" ]
        , HH.button
            [ HP.class_ (H.ClassName "btn btn--secondary")
            , HE.onClick \_ -> ShowComparison
            ]
            [ HH.text "Compare" ]
        ]
    ]

renderBranchTree :: forall m. String -> SessionTree -> Int -> H.ComponentHTML BranchAction () m
renderBranchTree branchId tree depth =
  let 
    branch = Map.lookup branchId tree.branches
    children = getChildBranches branchId tree
    isCurrent = tree.currentBranchId == branchId
  in
    case branch of
      Nothing -> HH.text ""
      Just b ->
        HH.div
          [ HP.class_ (H.ClassName "branch-item")
          , HP.style $ "padding-left: " <> show (depth * 16) <> "px"
          ]
          [ HH.div
              [ HP.classes $ branchItemClasses isCurrent
              , HE.onClick \_ -> SwitchBranch branchId
              ]
              [ HH.span [ HP.class_ (H.ClassName "branch-item__icon") ]
                  [ HH.text $ if depth == 0 then "🌿" else "└─ 🌿" ]
              , HH.span [ HP.class_ (H.ClassName "branch-item__name") ]
                  [ HH.text b.name ]
              , HH.span [ HP.class_ (H.ClassName "branch-item__stats") ]
                  [ HH.text $ show b.messageCount <> " msgs, " <> formatTokens b.tokenCount ]
              , when (not isCurrent) $
                  HH.button
                    [ HP.class_ (H.ClassName "branch-item__switch")
                    , HE.onClick \_ -> SwitchBranch branchId
                    ]
                    [ HH.text "Switch" ]
              ]
          , HH.div_ (map (\childId -> renderBranchTree childId tree (depth + 1)) children)
          ]
```

---

## Branch Operations

### Create Branch

```typescript
// bridge/src/session/branching.ts

export class SessionBranchManager {
  private store: StateStore;
  private db: Database;
  
  async createBranch(params: CreateBranchParams): Promise<SessionBranch> {
    const { sourceSessionId, branchPoint, name, description } = params;
    
    // Get source session
    const sourceSession = await this.db.getSession(sourceSessionId);
    if (!sourceSession) {
      throw new Error('Source session not found');
    }
    
    // Create new session as branch
    const branchId = generateId();
    const branchSession: Session = {
      id: branchId,
      title: sourceSession.title,
      branchName: name,
      parentSessionId: sourceSessionId,
      branchPoint,
      description,
      createdAt: new Date(),
      
      // Copy messages up to branch point
      messages: sourceSession.messages.slice(0, branchPoint + 1),
      
      // Copy metrics up to branch point
      promptTokens: this.sumTokens(sourceSession.messages.slice(0, branchPoint + 1), 'prompt'),
      completionTokens: this.sumTokens(sourceSession.messages.slice(0, branchPoint + 1), 'completion'),
      cost: this.sumCost(sourceSession.messages.slice(0, branchPoint + 1))
    };
    
    // Save to database
    await this.db.saveSession(branchSession);
    
    // Update session tree
    this.store.addBranch(branchSession);
    
    // Broadcast update
    this.wsManager.broadcast({
      jsonrpc: '2.0',
      method: 'session.branch.created',
      params: { branch: branchSession }
    });
    
    return branchSession;
  }
  
  async switchBranch(branchId: string): Promise<void> {
    const branch = await this.db.getSession(branchId);
    if (!branch) {
      throw new Error('Branch not found');
    }
    
    // Update current session
    this.store.setCurrentSession(branch);
    
    // Broadcast
    this.wsManager.broadcast({
      jsonrpc: '2.0',
      method: 'session.branch.switched',
      params: { branchId, session: branch }
    });
  }
  
  async compareBranches(branchA: string, branchB: string): Promise<BranchComparison> {
    const sessionA = await this.db.getSession(branchA);
    const sessionB = await this.db.getSession(branchB);
    
    // Find common ancestor
    const divergencePoint = this.findDivergencePoint(sessionA, sessionB);
    
    // Calculate diffs
    const messageDiff = sessionB.messages.length - sessionA.messages.length;
    const tokenDiff = (sessionB.promptTokens + sessionB.completionTokens) -
                     (sessionA.promptTokens + sessionA.completionTokens);
    const costDiff = sessionB.cost - sessionA.cost;
    
    // Get file changes
    const filesA = this.extractFileChanges(sessionA);
    const filesB = this.extractFileChanges(sessionB);
    const filesDiff = this.diffFiles(filesA, filesB);
    
    return {
      baseSession: sessionA,
      compareSession: sessionB,
      divergencePoint,
      metrics: { messageDiff, tokenDiff, costDiff, filesDiff: [...filesDiff.keys()] },
      fileDiffs: filesDiff
    };
  }
  
  async mergeBranch(request: MergeRequest): Promise<void> {
    const source = await this.db.getSession(request.sourceSessionId);
    const target = await this.db.getSession(request.targetSessionId);
    
    // Find messages to merge (after divergence point)
    const divergence = this.findDivergencePoint(source, target);
    const newMessages = source.messages.slice(divergence + 1);
    
    if (request.includeMessages) {
      // Append messages to target
      target.messages.push(...newMessages);
      target.promptTokens += this.sumTokens(newMessages, 'prompt');
      target.completionTokens += this.sumTokens(newMessages, 'completion');
      target.cost += this.sumCost(newMessages);
    }
    
    if (request.includeFileChanges) {
      // Apply file changes from source to target's context
      const fileChanges = this.extractFileChanges(source, divergence);
      for (const change of fileChanges) {
        await this.applyFileChange(change);
      }
    }
    
    // Save merged session
    await this.db.saveSession(target);
    
    // Optionally delete source branch
    // await this.db.deleteSession(source.id);
    
    this.wsManager.broadcast({
      jsonrpc: '2.0',
      method: 'session.branch.merged',
      params: { source: source.id, target: target.id }
    });
  }
}
```

---

## CSS Styling

```css
.branch-selector {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  overflow: hidden;
}

.branch-selector__header {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  padding: var(--space-3);
  background: var(--color-bg-elevated);
  border-bottom: 1px solid var(--color-border-subtle);
  cursor: pointer;
}

.branch-icon {
  font-size: 16px;
}

.branch-name {
  font-family: var(--font-mono);
  font-weight: var(--font-weight-medium);
  color: var(--color-success);
}

.branch-count {
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
}

.branch-item {
  border-bottom: 1px solid var(--color-border-subtle);
}

.branch-item:last-child {
  border-bottom: none;
}

.branch-item__row {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  padding: var(--space-2) var(--space-3);
  cursor: pointer;
  transition: background var(--transition-fast);
}

.branch-item__row:hover {
  background: var(--color-bg-hover);
}

.branch-item__row--current {
  background: var(--color-success-dim);
  border-left: 3px solid var(--color-success);
}

.branch-item__name {
  flex: 1;
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
}

.branch-item__stats {
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
}

.branch-item__switch {
  padding: 2px 8px;
  background: var(--color-bg-base);
  border: 1px solid var(--color-border-default);
  border-radius: 4px;
  font-size: var(--font-size-xs);
  color: var(--color-text-secondary);
  cursor: pointer;
}

.branch-item__switch:hover {
  background: var(--color-primary-dim);
  border-color: var(--color-primary);
  color: var(--color-primary);
}

.branch-comparison {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: var(--space-4);
}

.branch-comparison__card {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  padding: var(--space-3);
}

.branch-comparison__card--winner {
  border-color: var(--color-success);
  background: var(--color-success-dim);
}
```

---

## Keyboard Shortcuts

| Key | Action |
|-----|--------|
| `gb` | Show branch selector |
| `gB` | Create new branch |
| `[` | Previous branch |
| `]` | Next branch |
| `Ctrl+Shift+B` | Compare branches |

---

## Related Specifications

- `23-SESSION-MANAGEMENT.md` - Session basics
- `63-TIMELINE-VIEW.md` - Timeline integration
- `65-SESSION-RECORDING.md` - Recording branches

---

*"Every decision point is an opportunity to explore."*
