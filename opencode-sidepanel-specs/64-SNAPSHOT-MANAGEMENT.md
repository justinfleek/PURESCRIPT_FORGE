# 64-SNAPSHOT-MANAGEMENT: State Snapshots for Time Travel

## Overview

Snapshot Management handles creating, storing, and restoring complete application state snapshots, enabling the time-travel debugging feature in the Timeline view.

---

## Snapshot Types

### Automatic Snapshots
- Every 5 minutes of activity
- On session creation
- Every 5 messages
- On proof state changes
- On balance warnings/errors
- Before destructive operations

### Manual Snapshots
- User-created with description
- Named bookmarks for important points
- Can be starred/favorited

---

## Visual Design

### Snapshot Manager

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  SNAPSHOTS                              [+ Create Snapshot] [Settings ⚙]   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Storage: 45.2 MB / 100 MB                                                 │
│  ████████████████████████████████████████████░░░░░░░░░░░░░░ 45%            │
│                                                                             │
│  ┌─ TODAY (8 snapshots) ──────────────────────────────────────────────────┐│
│  │                                                                        ││
│  │  ◆ 3:45 PM  "Before refactoring auth"                        [Manual] ││
│  │    ★ Starred • 2.1 MB • Balance: 42.5 Diem • 12 messages              ││
│  │    [View] [Restore] [Compare] [Delete]                                ││
│  │                                                                        ││
│  │  ● 3:30 PM  Auto: Every 5 minutes                              [Auto] ││
│  │    1.8 MB • Balance: 45.2 Diem • 10 messages                          ││
│  │    [View] [Restore] [Compare] [Delete]                                ││
│  │                                                                        ││
│  │  ⚠ 3:15 PM  Auto: Balance warning                            [System] ││
│  │    1.5 MB • Balance: 5.0 Diem • 8 messages                            ││
│  │    [View] [Restore] [Compare] [Delete]                                ││
│  │                                                                        ││
│  │  ● 3:00 PM  Auto: Session started                            [System] ││
│  │    0.8 MB • Balance: 50.0 Diem • 0 messages                           ││
│  │    [View] [Restore] [Compare] [Delete]                                ││
│  │                                                                        ││
│  └────────────────────────────────────────────────────────────────────────┘│
│                                                                             │
│  ┌─ YESTERDAY (12 snapshots) ─────────────────────────────────────────────┐│
│  │  [Expand to view]                                                      ││
│  └────────────────────────────────────────────────────────────────────────┘│
│                                                                             │
│  ┌─ OLDER ───────────────────────────────────────────────────────────────┐ │
│  │  35 snapshots • 28.4 MB • [View All] [Clean Up...]                    │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Create Snapshot Modal

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  CREATE SNAPSHOT                                                       [✕] │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Description (optional):                                                   │
│  ┌─────────────────────────────────────────────────────────────────────┐  │
│  │ Before refactoring auth module                                      │  │
│  └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  ┌─ CURRENT STATE ───────────────────────────────────────────────────────┐ │
│  │  Balance: 42.5 Diem                                                   │ │
│  │  Session: Debug Auth (12 messages, 23,955 tokens)                    │ │
│  │  Files in context: 8                                                  │ │
│  │  Proof goals: 2                                                       │ │
│  │  Estimated size: ~2.1 MB                                              │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  Options:                                                                  │
│  [✓] Include message content                                               │
│  [✓] Include file context                                                  │
│  [ ] Include terminal history                                              │
│  [✓] Star this snapshot                                                    │
│                                                                             │
│  [Cancel]                                              [Create Snapshot]   │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Data Model

```typescript
interface Snapshot {
  id: string;
  timestamp: Date;
  
  // Metadata
  type: 'auto' | 'manual' | 'system';
  trigger: SnapshotTrigger;
  description?: string;
  starred: boolean;
  
  // Size tracking
  sizeBytes: number;
  
  // State data
  state: SnapshotState;
  
  // Quick access fields (for listing without loading full state)
  summary: SnapshotSummary;
}

type SnapshotTrigger =
  | { type: 'interval' }
  | { type: 'session_created'; sessionId: string }
  | { type: 'message_count'; count: number }
  | { type: 'proof_changed'; file: string }
  | { type: 'balance_warning'; level: 'warning' | 'critical' }
  | { type: 'manual'; description: string }
  | { type: 'before_restore'; targetSnapshotId: string };

interface SnapshotState {
  // Core state
  balance: BalanceState;
  session: SessionState | null;
  
  // Optional state (based on options)
  messages?: Message[];
  fileContext?: ContextEntry[];
  terminalHistory?: string;
  proofState?: ProofState;
  
  // Metrics at snapshot time
  metrics: MetricsSnapshot;
}

interface SnapshotSummary {
  balanceDiem: number;
  messageCount: number;
  tokenCount: number;
  filesInContext: number;
  proofGoals: number;
  hasWarning: boolean;
  hasError: boolean;
}

interface SnapshotOptions {
  includeMessages: boolean;
  includeFileContext: boolean;
  includeTerminalHistory: boolean;
  starred: boolean;
}

interface SnapshotComparison {
  from: Snapshot;
  to: Snapshot;
  
  changes: {
    balance: {
      before: number;
      after: number;
      delta: number;
    };
    messages: {
      added: number;
      removed: number;
    };
    tokens: {
      before: number;
      after: number;
      delta: number;
    };
    files: {
      added: string[];
      removed: string[];
    };
    proofGoals: {
      before: number;
      after: number;
    };
  };
}
```

---

## PureScript Types

```purescript
module Sidepanel.Snapshots where

import Prelude
import Data.DateTime (DateTime)
import Data.Maybe (Maybe)

data SnapshotType = Auto | Manual | System

data SnapshotTrigger
  = IntervalTrigger
  | SessionCreated String
  | MessageCount Int
  | ProofChanged String
  | BalanceWarning AlertLevel
  | ManualTrigger String
  | BeforeRestore String

type Snapshot =
  { id :: String
  , timestamp :: DateTime
  , snapshotType :: SnapshotType
  , trigger :: SnapshotTrigger
  , description :: Maybe String
  , starred :: Boolean
  , sizeBytes :: Int
  , summary :: SnapshotSummary
  }

type SnapshotSummary =
  { balanceDiem :: Number
  , messageCount :: Int
  , tokenCount :: Int
  , filesInContext :: Int
  , proofGoals :: Int
  , hasWarning :: Boolean
  , hasError :: Boolean
  }

type SnapshotState =
  { balance :: BalanceState
  , session :: Maybe SessionState
  , messages :: Maybe (Array Message)
  , fileContext :: Maybe (Array ContextEntry)
  , proofState :: Maybe ProofState
  }

-- Manager state
type SnapshotManagerState =
  { snapshots :: Array Snapshot
  , totalSizeBytes :: Int
  , maxSizeBytes :: Int
  , isLoading :: Boolean
  , selectedId :: Maybe String
  , compareMode :: Boolean
  , compareIds :: Maybe (Tuple String String)
  }

data Action
  = Initialize
  | LoadSnapshots
  | SnapshotsLoaded (Array Snapshot)
  | CreateSnapshot SnapshotOptions
  | SnapshotCreated Snapshot
  | DeleteSnapshot String
  | RestoreSnapshot String
  | ToggleStar String
  | SelectSnapshot String
  | EnterCompareMode
  | ExitCompareMode
  | SetCompareSnapshots String String
  | CleanUpOld Int  -- days to keep
```

---

## Bridge Implementation

```typescript
// bridge/src/snapshots/manager.ts

export class SnapshotManager {
  private db: Database;
  private store: StateStore;
  private maxStorageBytes: number;
  private autoSnapshotInterval: number;
  private lastAutoSnapshot: Date | null = null;
  private messagesSinceSnapshot: number = 0;
  
  constructor(config: SnapshotConfig) {
    this.db = config.db;
    this.store = config.store;
    this.maxStorageBytes = config.maxStorageBytes ?? 100 * 1024 * 1024;  // 100MB
    this.autoSnapshotInterval = config.autoSnapshotInterval ?? 5 * 60 * 1000;  // 5 min
    
    this.setupAutoSnapshots();
    this.setupTriggers();
  }
  
  private setupAutoSnapshots(): void {
    setInterval(() => {
      const state = this.store.getState();
      if (state.session) {  // Only if there's an active session
        this.createSnapshot({
          trigger: { type: 'interval' },
          options: {
            includeMessages: true,
            includeFileContext: true,
            includeTerminalHistory: false,
            starred: false
          }
        });
      }
    }, this.autoSnapshotInterval);
  }
  
  private setupTriggers(): void {
    // Session created
    this.store.on('session.created', (session) => {
      this.createSnapshot({
        trigger: { type: 'session_created', sessionId: session.id },
        options: defaultOptions
      });
    });
    
    // Message count
    this.store.on('message.completed', () => {
      this.messagesSinceSnapshot++;
      if (this.messagesSinceSnapshot >= 5) {
        this.createSnapshot({
          trigger: { type: 'message_count', count: this.messagesSinceSnapshot },
          options: defaultOptions
        });
        this.messagesSinceSnapshot = 0;
      }
    });
    
    // Balance warning
    this.store.on('balance.update', (balance) => {
      if (balance.alertLevel === 'warning' || balance.alertLevel === 'critical') {
        // Don't spam snapshots - only if alert level changed
        if (this.lastAlertLevel !== balance.alertLevel) {
          this.createSnapshot({
            trigger: { type: 'balance_warning', level: balance.alertLevel },
            options: defaultOptions
          });
          this.lastAlertLevel = balance.alertLevel;
        }
      }
    });
    
    // Proof changed
    this.store.on('proof.update', (proof) => {
      this.createSnapshot({
        trigger: { type: 'proof_changed', file: proof.file },
        options: { ...defaultOptions, starred: false }
      });
    });
  }
  
  async createSnapshot(params: CreateSnapshotParams): Promise<Snapshot> {
    const state = this.store.getState();
    const now = new Date();
    
    // Build snapshot state based on options
    const snapshotState: SnapshotState = {
      balance: state.balance,
      session: state.session,
      messages: params.options.includeMessages ? state.session?.messages : undefined,
      fileContext: params.options.includeFileContext ? state.context?.entries : undefined,
      proofState: state.proof
    };
    
    // Calculate size
    const stateJson = JSON.stringify(snapshotState);
    const sizeBytes = new Blob([stateJson]).size;
    
    // Check storage limit
    await this.enforceStorageLimit(sizeBytes);
    
    // Create snapshot
    const snapshot: Snapshot = {
      id: generateId(),
      timestamp: now,
      type: params.manual ? 'manual' : 'auto',
      trigger: params.trigger,
      description: params.description,
      starred: params.options.starred,
      sizeBytes,
      state: snapshotState,
      summary: this.buildSummary(snapshotState)
    };
    
    // Save to database
    await this.db.run(`
      INSERT INTO snapshots (id, timestamp, type, trigger, description, starred, size_bytes, state_json, summary_json)
      VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    `, [
      snapshot.id,
      snapshot.timestamp.toISOString(),
      snapshot.type,
      JSON.stringify(snapshot.trigger),
      snapshot.description,
      snapshot.starred ? 1 : 0,
      snapshot.sizeBytes,
      stateJson,
      JSON.stringify(snapshot.summary)
    ]);
    
    this.lastAutoSnapshot = now;
    
    // Broadcast
    this.broadcastSnapshotCreated(snapshot);
    
    return snapshot;
  }
  
  async restoreSnapshot(snapshotId: string): Promise<void> {
    // Create "before restore" snapshot
    await this.createSnapshot({
      trigger: { type: 'before_restore', targetSnapshotId: snapshotId },
      options: { ...defaultOptions, includeMessages: true }
    });
    
    // Load snapshot
    const snapshot = await this.getSnapshot(snapshotId);
    if (!snapshot) {
      throw new Error(`Snapshot not found: ${snapshotId}`);
    }
    
    // Restore state
    this.store.setState({
      balance: snapshot.state.balance,
      session: snapshot.state.session
    });
    
    // Broadcast
    this.broadcastSnapshotRestored(snapshotId);
  }
  
  async compareSnapshots(fromId: string, toId: string): Promise<SnapshotComparison> {
    const from = await this.getSnapshot(fromId);
    const to = await this.getSnapshot(toId);
    
    if (!from || !to) {
      throw new Error('Snapshot not found');
    }
    
    return {
      from,
      to,
      changes: {
        balance: {
          before: from.summary.balanceDiem,
          after: to.summary.balanceDiem,
          delta: to.summary.balanceDiem - from.summary.balanceDiem
        },
        messages: {
          added: Math.max(0, to.summary.messageCount - from.summary.messageCount),
          removed: Math.max(0, from.summary.messageCount - to.summary.messageCount)
        },
        tokens: {
          before: from.summary.tokenCount,
          after: to.summary.tokenCount,
          delta: to.summary.tokenCount - from.summary.tokenCount
        },
        files: this.diffFiles(from.state.fileContext, to.state.fileContext),
        proofGoals: {
          before: from.summary.proofGoals,
          after: to.summary.proofGoals
        }
      }
    };
  }
  
  private async enforceStorageLimit(newBytes: number): Promise<void> {
    const totalSize = await this.getTotalSize();
    
    if (totalSize + newBytes > this.maxStorageBytes) {
      // Delete oldest non-starred snapshots until under limit
      const toDelete = await this.db.all(`
        SELECT id, size_bytes FROM snapshots
        WHERE starred = 0
        ORDER BY timestamp ASC
      `);
      
      let freed = 0;
      for (const snap of toDelete) {
        if (totalSize + newBytes - freed <= this.maxStorageBytes) {
          break;
        }
        await this.deleteSnapshot(snap.id);
        freed += snap.size_bytes;
      }
    }
  }
  
  private buildSummary(state: SnapshotState): SnapshotSummary {
    return {
      balanceDiem: state.balance.diem,
      messageCount: state.session?.messages?.length ?? 0,
      tokenCount: (state.session?.promptTokens ?? 0) + (state.session?.completionTokens ?? 0),
      filesInContext: state.fileContext?.length ?? 0,
      proofGoals: state.proofState?.goals?.length ?? 0,
      hasWarning: state.balance.alertLevel === 'warning',
      hasError: state.balance.alertLevel === 'critical'
    };
  }
}
```

---

## SQLite Schema

```sql
CREATE TABLE IF NOT EXISTS snapshots (
  id TEXT PRIMARY KEY,
  timestamp TEXT NOT NULL,
  type TEXT NOT NULL,  -- 'auto', 'manual', 'system'
  trigger TEXT NOT NULL,  -- JSON
  description TEXT,
  starred INTEGER DEFAULT 0,
  size_bytes INTEGER NOT NULL,
  state_json TEXT NOT NULL,
  summary_json TEXT NOT NULL,
  
  -- Indexes for quick filtering
  created_at DATETIME DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX idx_snapshots_timestamp ON snapshots(timestamp DESC);
CREATE INDEX idx_snapshots_starred ON snapshots(starred);
CREATE INDEX idx_snapshots_type ON snapshots(type);
```

---

## Related Specifications

- `63-TIMELINE-VIEW.md` - Timeline display
- `34-DATABASE-SCHEMA.md` - Database structure
- `32-STATE-SYNCHRONIZATION.md` - State management

---

*"Every state can be saved. Every decision can be undone."*
