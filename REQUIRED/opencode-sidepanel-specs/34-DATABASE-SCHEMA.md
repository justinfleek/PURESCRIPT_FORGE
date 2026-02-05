# 34-DATABASE-SCHEMA: SQLite Storage Schema

## Overview

The bridge server uses SQLite for local persistence of sessions, messages, metrics, snapshots, and recordings. This document defines all tables and their relationships.

---

## Schema Overview

```
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│    sessions     │────<│    messages     │────<│   tool_calls    │
└─────────────────┘     └─────────────────┘     └─────────────────┘
        │                       │
        │                       │
        ▼                       ▼
┌─────────────────┐     ┌─────────────────┐
│ session_branches│     │ message_metrics │
└─────────────────┘     └─────────────────┘

┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│    snapshots    │     │   recordings    │────<│ recording_events│
└─────────────────┘     └─────────────────┘     └─────────────────┘

┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│ balance_history │     │  hourly_stats   │     │  daily_stats    │
└─────────────────┘     └─────────────────┘     └─────────────────┘

┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│  context_files  │     │   file_diffs    │     │   diff_hunks    │
└─────────────────┘     └─────────────────┘     └─────────────────┘
```

---

## Core Tables

### Sessions

```sql
CREATE TABLE sessions (
  id TEXT PRIMARY KEY,
  title TEXT NOT NULL,
  icon TEXT DEFAULT '💬',
  color TEXT,
  
  -- Model info
  model TEXT NOT NULL,
  provider TEXT NOT NULL,
  
  -- Branching
  parent_id TEXT REFERENCES sessions(id),
  branch_point INTEGER,  -- Message index where branched
  
  -- Status
  status TEXT NOT NULL DEFAULT 'active' 
    CHECK (status IN ('active', 'idle', 'archived', 'deleted')),
  
  -- Aggregates (denormalized for performance)
  message_count INTEGER DEFAULT 0,
  prompt_tokens INTEGER DEFAULT 0,
  completion_tokens INTEGER DEFAULT 0,
  cost REAL DEFAULT 0,
  
  -- Timestamps
  created_at TEXT NOT NULL DEFAULT (datetime('now')),
  updated_at TEXT NOT NULL DEFAULT (datetime('now')),
  
  -- Indexes
  FOREIGN KEY (parent_id) REFERENCES sessions(id) ON DELETE SET NULL
);

CREATE INDEX idx_sessions_status ON sessions(status);
CREATE INDEX idx_sessions_parent ON sessions(parent_id);
CREATE INDEX idx_sessions_updated ON sessions(updated_at DESC);
```

### Messages

```sql
CREATE TABLE messages (
  id TEXT PRIMARY KEY,
  session_id TEXT NOT NULL REFERENCES sessions(id) ON DELETE CASCADE,
  
  -- Content
  role TEXT NOT NULL CHECK (role IN ('user', 'assistant', 'system', 'tool')),
  content TEXT NOT NULL,
  
  -- For tool messages
  tool_call_id TEXT,
  
  -- Usage (for assistant messages)
  prompt_tokens INTEGER,
  completion_tokens INTEGER,
  model TEXT,
  cost REAL,
  
  -- Timing
  started_at TEXT,
  completed_at TEXT,
  duration_ms INTEGER,
  
  -- Ordering
  sequence INTEGER NOT NULL,
  
  -- Timestamps
  created_at TEXT NOT NULL DEFAULT (datetime('now')),
  
  FOREIGN KEY (session_id) REFERENCES sessions(id) ON DELETE CASCADE
);

CREATE INDEX idx_messages_session ON messages(session_id, sequence);
CREATE INDEX idx_messages_role ON messages(role);
```

### Tool Calls

```sql
CREATE TABLE tool_calls (
  id TEXT PRIMARY KEY,
  message_id TEXT NOT NULL REFERENCES messages(id) ON DELETE CASCADE,
  
  -- Tool info
  name TEXT NOT NULL,
  arguments TEXT,  -- JSON
  result TEXT,     -- JSON or string
  
  -- Status
  status TEXT NOT NULL DEFAULT 'pending'
    CHECK (status IN ('pending', 'running', 'completed', 'error')),
  error TEXT,
  
  -- Timing
  started_at TEXT,
  completed_at TEXT,
  duration_ms INTEGER,
  
  -- Ordering (for multiple tools in one message)
  sequence INTEGER NOT NULL DEFAULT 0,
  
  FOREIGN KEY (message_id) REFERENCES messages(id) ON DELETE CASCADE
);

CREATE INDEX idx_tool_calls_message ON tool_calls(message_id);
CREATE INDEX idx_tool_calls_name ON tool_calls(name);
```

---

## Metrics Tables

### Message Metrics

```sql
CREATE TABLE message_metrics (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  message_id TEXT NOT NULL REFERENCES messages(id) ON DELETE CASCADE,
  session_id TEXT NOT NULL REFERENCES sessions(id) ON DELETE CASCADE,
  
  -- Timing
  timestamp TEXT NOT NULL,
  
  -- Model
  model TEXT NOT NULL,
  provider TEXT NOT NULL,
  
  -- Token counts
  prompt_tokens INTEGER NOT NULL,
  completion_tokens INTEGER NOT NULL,
  cached_tokens INTEGER DEFAULT 0,
  
  -- Cost
  cost REAL NOT NULL,
  
  -- Performance
  first_token_ms INTEGER,  -- Time to first token
  total_ms INTEGER,        -- Total response time
  tokens_per_second REAL,
  
  FOREIGN KEY (message_id) REFERENCES messages(id) ON DELETE CASCADE,
  FOREIGN KEY (session_id) REFERENCES sessions(id) ON DELETE CASCADE
);

CREATE INDEX idx_message_metrics_session ON message_metrics(session_id);
CREATE INDEX idx_message_metrics_timestamp ON message_metrics(timestamp);
CREATE INDEX idx_message_metrics_model ON message_metrics(model);
```

### Balance History

```sql
CREATE TABLE balance_history (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  timestamp TEXT NOT NULL DEFAULT (datetime('now')),
  
  -- Balance values
  diem REAL NOT NULL,
  usd REAL,
  effective REAL,
  
  -- Source of update
  source TEXT CHECK (source IN ('api_response', 'manual', 'sync')),
  
  -- Associated message (if from API response)
  message_id TEXT REFERENCES messages(id) ON DELETE SET NULL
);

CREATE INDEX idx_balance_history_timestamp ON balance_history(timestamp DESC);
```

### Hourly Stats

```sql
CREATE TABLE hourly_stats (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  hour TEXT NOT NULL,  -- ISO format truncated to hour: 2025-01-15T10:00:00
  
  -- Token aggregates
  prompt_tokens INTEGER DEFAULT 0,
  completion_tokens INTEGER DEFAULT 0,
  total_tokens INTEGER DEFAULT 0,
  
  -- Cost
  total_cost REAL DEFAULT 0,
  
  -- Counts
  message_count INTEGER DEFAULT 0,
  session_count INTEGER DEFAULT 0,
  
  -- Balance change
  diem_start REAL,
  diem_end REAL,
  diem_consumed REAL,
  
  UNIQUE(hour)
);

CREATE INDEX idx_hourly_stats_hour ON hourly_stats(hour DESC);
```

### Daily Stats

```sql
CREATE TABLE daily_stats (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  date TEXT NOT NULL,  -- ISO format: 2025-01-15
  
  -- Token aggregates
  prompt_tokens INTEGER DEFAULT 0,
  completion_tokens INTEGER DEFAULT 0,
  total_tokens INTEGER DEFAULT 0,
  
  -- Cost
  total_cost REAL DEFAULT 0,
  
  -- Counts
  message_count INTEGER DEFAULT 0,
  session_count INTEGER DEFAULT 0,
  tool_call_count INTEGER DEFAULT 0,
  
  -- Balance
  diem_start REAL,
  diem_end REAL,
  diem_consumed REAL,
  
  -- By model breakdown (JSON)
  by_model TEXT,  -- { "llama-3.3-70b": { tokens: 1000, cost: 0.01 }, ... }
  
  UNIQUE(date)
);

CREATE INDEX idx_daily_stats_date ON daily_stats(date DESC);
```

---

## Snapshot Tables

### Snapshots (for Timeline)

```sql
CREATE TABLE snapshots (
  id TEXT PRIMARY KEY,
  timestamp TEXT NOT NULL DEFAULT (datetime('now')),
  
  -- Trigger
  trigger TEXT NOT NULL CHECK (trigger IN (
    'auto',           -- Automatic periodic
    'manual',         -- User requested
    'session_start',  -- New session
    'message_count',  -- Every N messages
    'balance_low',    -- Balance warning
    'error'           -- On error
  )),
  
  -- Description (for manual snapshots)
  description TEXT,
  
  -- Full state (JSON)
  state_json TEXT NOT NULL,
  
  -- Quick access fields (denormalized from state_json)
  balance_diem REAL,
  session_id TEXT,
  session_message_count INTEGER,
  
  -- Flags
  has_warning BOOLEAN DEFAULT FALSE,
  has_error BOOLEAN DEFAULT FALSE
);

CREATE INDEX idx_snapshots_timestamp ON snapshots(timestamp DESC);
CREATE INDEX idx_snapshots_session ON snapshots(session_id);
```

---

## Recording Tables

### Recordings

```sql
CREATE TABLE recordings (
  id TEXT PRIMARY KEY,
  title TEXT NOT NULL,
  description TEXT,
  
  -- Metadata
  duration_ms INTEGER NOT NULL,
  total_tokens INTEGER NOT NULL,
  total_cost REAL NOT NULL,
  
  -- Tags (JSON array)
  tags TEXT DEFAULT '[]',
  
  -- Rating (1-5 stars)
  rating INTEGER DEFAULT 0 CHECK (rating >= 0 AND rating <= 5),
  
  -- Associated session
  session_id TEXT REFERENCES sessions(id) ON DELETE SET NULL,
  
  -- Export/Share
  exported_at TEXT,
  share_url TEXT,
  
  -- Timestamps
  created_at TEXT NOT NULL DEFAULT (datetime('now')),
  updated_at TEXT NOT NULL DEFAULT (datetime('now'))
);

CREATE INDEX idx_recordings_created ON recordings(created_at DESC);
CREATE INDEX idx_recordings_session ON recordings(session_id);
```

### Recording Events

```sql
CREATE TABLE recording_events (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  recording_id TEXT NOT NULL REFERENCES recordings(id) ON DELETE CASCADE,
  
  -- Timing (ms from recording start)
  timestamp_ms INTEGER NOT NULL,
  
  -- Event type
  event_type TEXT NOT NULL CHECK (event_type IN (
    'message.user',
    'message.assistant.start',
    'message.assistant.chunk',
    'message.assistant.complete',
    'tool.start',
    'tool.complete',
    'balance.update',
    'proof.update',
    'error'
  )),
  
  -- Event data (JSON)
  data TEXT NOT NULL,
  
  FOREIGN KEY (recording_id) REFERENCES recordings(id) ON DELETE CASCADE
);

CREATE INDEX idx_recording_events_recording ON recording_events(recording_id, timestamp_ms);
```

### Recording Markers

```sql
CREATE TABLE recording_markers (
  id TEXT PRIMARY KEY,
  recording_id TEXT NOT NULL REFERENCES recordings(id) ON DELETE CASCADE,
  
  -- Position (ms from start)
  timestamp_ms INTEGER NOT NULL,
  
  -- Display
  label TEXT NOT NULL,
  color TEXT DEFAULT '#8b5cf6',
  
  FOREIGN KEY (recording_id) REFERENCES recordings(id) ON DELETE CASCADE
);

CREATE INDEX idx_recording_markers_recording ON recording_markers(recording_id);
```

---

## Context and Diff Tables

### Context Files

```sql
CREATE TABLE context_files (
  id TEXT PRIMARY KEY,
  session_id TEXT NOT NULL REFERENCES sessions(id) ON DELETE CASCADE,
  
  -- File info
  path TEXT NOT NULL,
  relative_path TEXT NOT NULL,
  language TEXT,
  
  -- Token tracking
  tokens INTEGER NOT NULL,
  
  -- State
  status TEXT NOT NULL DEFAULT 'in-context'
    CHECK (status IN ('reading', 'in-context', 'stale', 'removed')),
  source TEXT NOT NULL CHECK (source IN ('user-added', 'ai-read', 'ai-written', 'preset')),
  
  -- Timing
  added_at TEXT NOT NULL DEFAULT (datetime('now')),
  last_read_at TEXT,
  last_referenced_at TEXT,
  
  -- Content hash (to detect changes)
  content_hash TEXT,
  
  FOREIGN KEY (session_id) REFERENCES sessions(id) ON DELETE CASCADE,
  UNIQUE(session_id, path)
);

CREATE INDEX idx_context_files_session ON context_files(session_id);
```

### File Diffs

```sql
CREATE TABLE file_diffs (
  id TEXT PRIMARY KEY,
  session_id TEXT NOT NULL REFERENCES sessions(id) ON DELETE CASCADE,
  message_id TEXT REFERENCES messages(id) ON DELETE SET NULL,
  
  -- File info
  path TEXT NOT NULL,
  status TEXT NOT NULL CHECK (status IN ('modified', 'created', 'deleted', 'renamed')),
  old_path TEXT,  -- For renames
  
  -- AI explanation
  description TEXT,
  reason TEXT,
  
  -- Review status
  review_status TEXT NOT NULL DEFAULT 'pending'
    CHECK (review_status IN ('pending', 'accepted', 'rejected', 'partial')),
  
  -- Timestamp
  created_at TEXT NOT NULL DEFAULT (datetime('now')),
  
  FOREIGN KEY (session_id) REFERENCES sessions(id) ON DELETE CASCADE,
  FOREIGN KEY (message_id) REFERENCES messages(id) ON DELETE SET NULL
);

CREATE INDEX idx_file_diffs_session ON file_diffs(session_id);
CREATE INDEX idx_file_diffs_status ON file_diffs(review_status);
```

### Diff Hunks

```sql
CREATE TABLE diff_hunks (
  id TEXT PRIMARY KEY,
  diff_id TEXT NOT NULL REFERENCES file_diffs(id) ON DELETE CASCADE,
  
  -- Position
  start_line INTEGER NOT NULL,
  end_line INTEGER NOT NULL,
  
  -- Content (JSON array of lines)
  lines TEXT NOT NULL,
  
  -- AI explanation
  explanation TEXT,
  
  -- Status
  status TEXT NOT NULL DEFAULT 'pending'
    CHECK (status IN ('pending', 'accepted', 'rejected')),
  
  -- Ordering
  sequence INTEGER NOT NULL DEFAULT 0,
  
  FOREIGN KEY (diff_id) REFERENCES file_diffs(id) ON DELETE CASCADE
);

CREATE INDEX idx_diff_hunks_diff ON diff_hunks(diff_id);
```

---

## Search Index (FTS5)

```sql
-- Full-text search for messages
CREATE VIRTUAL TABLE messages_fts USING fts5(
  content,
  session_id UNINDEXED,
  message_id UNINDEXED,
  content='messages',
  content_rowid='rowid'
);

-- Triggers to keep FTS in sync
CREATE TRIGGER messages_ai AFTER INSERT ON messages BEGIN
  INSERT INTO messages_fts(rowid, content, session_id, message_id)
  VALUES (new.rowid, new.content, new.session_id, new.id);
END;

CREATE TRIGGER messages_ad AFTER DELETE ON messages BEGIN
  INSERT INTO messages_fts(messages_fts, rowid, content, session_id, message_id)
  VALUES ('delete', old.rowid, old.content, old.session_id, old.id);
END;

CREATE TRIGGER messages_au AFTER UPDATE ON messages BEGIN
  INSERT INTO messages_fts(messages_fts, rowid, content, session_id, message_id)
  VALUES ('delete', old.rowid, old.content, old.session_id, old.id);
  INSERT INTO messages_fts(rowid, content, session_id, message_id)
  VALUES (new.rowid, new.content, new.session_id, new.id);
END;

-- Full-text search for sessions
CREATE VIRTUAL TABLE sessions_fts USING fts5(
  title,
  session_id UNINDEXED,
  content='sessions',
  content_rowid='rowid'
);
```

---

## Migrations

```typescript
// bridge/src/db/migrations.ts

export const migrations: Migration[] = [
  {
    version: 1,
    up: `
      -- Initial schema
      CREATE TABLE sessions (...);
      CREATE TABLE messages (...);
      CREATE TABLE tool_calls (...);
    `
  },
  {
    version: 2,
    up: `
      -- Add metrics tables
      CREATE TABLE message_metrics (...);
      CREATE TABLE balance_history (...);
      CREATE TABLE hourly_stats (...);
      CREATE TABLE daily_stats (...);
    `
  },
  {
    version: 3,
    up: `
      -- Add recording support
      CREATE TABLE recordings (...);
      CREATE TABLE recording_events (...);
      CREATE TABLE recording_markers (...);
    `
  },
  {
    version: 4,
    up: `
      -- Add context and diff tracking
      CREATE TABLE context_files (...);
      CREATE TABLE file_diffs (...);
      CREATE TABLE diff_hunks (...);
    `
  },
  {
    version: 5,
    up: `
      -- Add full-text search
      CREATE VIRTUAL TABLE messages_fts USING fts5(...);
      CREATE VIRTUAL TABLE sessions_fts USING fts5(...);
    `
  }
];
```

---

## Related Specifications

- `30-BRIDGE-ARCHITECTURE.md` - Bridge design
- `13-TOKEN-USAGE-METRICS.md` - Metrics collection
- `65-SESSION-RECORDING.md` - Recording system

---

*"A well-designed schema is the foundation of a fast application."*
