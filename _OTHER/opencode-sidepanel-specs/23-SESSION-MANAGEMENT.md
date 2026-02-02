# 23-SESSION-MANAGEMENT: Conversation Tracking and Persistence

## Overview

Session management tracks the complete lifecycle of OpenCode conversations—from creation through messages to completion. Every token, every cost, every tool call is captured and persisted for visualization, export, and time-travel debugging.

---

## Session Lifecycle

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         SESSION LIFECYCLE                               │
│                                                                          │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐          │
│  │ CREATED  │───▶│  ACTIVE  │───▶│ PAUSED   │───▶│ COMPLETED│          │
│  └──────────┘    └──────────┘    └──────────┘    └──────────┘          │
│       │               │               │               │                  │
│       │               │               │               │                  │
│       ▼               ▼               ▼               ▼                  │
│  session.created  message.*      session.updated  session.completed     │
│  event            events         (user switches)  (explicit end)        │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### States

| State | Description | Transitions |
|-------|-------------|-------------|
| `created` | Session initialized, no messages yet | → `active` on first message |
| `active` | Messages being exchanged | → `paused`, → `completed` |
| `paused` | User switched to different session | → `active` on resume |
| `completed` | Session explicitly ended or timed out | Terminal state |

---

## Data Model

### Session

```typescript
interface Session {
  // Identity
  id: string;              // UUID from OpenCode
  name: string;            // User-provided or auto-generated
  
  // Timing
  createdAt: Date;
  updatedAt: Date;
  completedAt: Date | null;
  
  // Model info
  model: string;           // e.g., "llama-3.3-70b"
  provider: string;        // e.g., "venice"
  
  // Token tracking
  promptTokens: number;    // Total input tokens
  completionTokens: number;// Total output tokens
  totalTokens: number;     // promptTokens + completionTokens
  
  // Cost tracking  
  cost: number;            // Total cost in USD
  diemUsed: number;        // Diem consumed (if applicable)
  
  // Message tracking
  messageCount: number;
  messages: Message[];     // Full message history
  
  // Tool tracking
  toolCalls: ToolCall[];   // All tool invocations
  
  // Metadata
  metadata: Record<string, unknown>;
  tags: string[];
}
```

### Message

```typescript
interface Message {
  // Identity
  id: string;
  sessionId: string;
  
  // Content
  role: 'user' | 'assistant' | 'system' | 'tool';
  content: string;
  
  // Timing
  createdAt: Date;
  completedAt: Date | null;
  duration: number | null;  // ms from start to complete
  
  // Status
  status: 'pending' | 'streaming' | 'completed' | 'error' | 'cancelled';
  error: MessageError | null;
  
  // Usage (for assistant messages)
  usage: TokenUsage | null;
  
  // Tool calls (for assistant messages)
  toolCalls: ToolCallRef[];
  
  // Cost
  cost: number;
}

interface TokenUsage {
  promptTokens: number;
  completionTokens: number;
  totalTokens: number;
}

interface MessageError {
  code: string;
  message: string;
  retryable: boolean;
}
```

### Tool Call

```typescript
interface ToolCall {
  id: string;
  sessionId: string;
  messageId: string;
  
  // Tool info
  tool: string;            // Tool name (e.g., "read_file", "lean_goal")
  category: ToolCategory;
  
  // Timing
  startedAt: Date;
  completedAt: Date | null;
  duration: number | null;
  
  // Input/Output
  input: Record<string, unknown>;
  output: unknown | null;
  
  // Status
  status: 'running' | 'completed' | 'error';
  error: string | null;
}

type ToolCategory = 
  | 'file'      // read_file, write_file, etc.
  | 'shell'     // bash, exec
  | 'search'    // grep, find
  | 'lean'      // lean_goal, lean_completions
  | 'mcp'       // other MCP tools
  | 'internal'; // OpenCode internal tools
```

---

## Event Handling

### OpenCode Events → Session State

```typescript
// bridge/src/session/manager.ts

export class SessionManager {
  private store: StateStore;
  private db: Database;
  private activeSession: Session | null = null;
  
  constructor(store: StateStore, db: Database) {
    this.store = store;
    this.db = db;
  }
  
  // ─── Session Events ───
  
  handleSessionCreated(event: SessionCreatedEvent): void {
    const session: Session = {
      id: event.session.id,
      name: event.session.name ?? `Session ${new Date().toISOString()}`,
      createdAt: new Date(),
      updatedAt: new Date(),
      completedAt: null,
      model: event.session.model,
      provider: 'venice',
      promptTokens: 0,
      completionTokens: 0,
      totalTokens: 0,
      cost: 0,
      diemUsed: 0,
      messageCount: 0,
      messages: [],
      toolCalls: [],
      metadata: event.session.metadata ?? {},
      tags: []
    };
    
    this.activeSession = session;
    this.db.sessions.insert(session);
    this.store.updateSession(session);
    this.broadcast({ type: 'session.created', session });
  }
  
  handleSessionUpdated(event: SessionUpdatedEvent): void {
    if (!this.activeSession) return;
    
    const updates = {
      updatedAt: new Date(),
      ...event.changes
    };
    
    this.activeSession = { ...this.activeSession, ...updates };
    this.db.sessions.update(this.activeSession.id, updates);
    this.store.updateSession(this.activeSession);
  }
  
  handleSessionCompleted(event: SessionCompletedEvent): void {
    if (!this.activeSession) return;
    
    this.activeSession = {
      ...this.activeSession,
      completedAt: new Date(),
      updatedAt: new Date()
    };
    
    this.db.sessions.update(this.activeSession.id, {
      completedAt: this.activeSession.completedAt
    });
    
    this.broadcast({ type: 'session.completed', session: this.activeSession });
    this.activeSession = null;
    this.store.updateSession(null);
  }
  
  // ─── Message Events ───
  
  handleMessageCreated(event: MessageCreatedEvent): void {
    if (!this.activeSession) return;
    
    const message: Message = {
      id: event.message.id,
      sessionId: this.activeSession.id,
      role: event.message.role,
      content: event.message.content,
      createdAt: new Date(),
      completedAt: null,
      duration: null,
      status: 'pending',
      error: null,
      usage: null,
      toolCalls: [],
      cost: 0
    };
    
    this.activeSession.messages.push(message);
    this.activeSession.messageCount++;
    this.db.messages.insert(message);
    
    this.broadcast({ type: 'message.created', message });
  }
  
  handleMessageCompleted(event: MessageCompletedEvent): void {
    if (!this.activeSession) return;
    
    const message = this.activeSession.messages.find(m => m.id === event.message.id);
    if (!message) return;
    
    const now = new Date();
    const duration = now.getTime() - message.createdAt.getTime();
    
    // Calculate cost based on usage
    const cost = event.message.usage 
      ? this.calculateCost(event.message.usage, this.activeSession.model)
      : 0;
    
    // Update message
    Object.assign(message, {
      content: event.message.content,
      completedAt: now,
      duration,
      status: 'completed',
      usage: event.message.usage,
      cost
    });
    
    // Update session totals
    if (event.message.usage) {
      this.activeSession.promptTokens += event.message.usage.promptTokens;
      this.activeSession.completionTokens += event.message.usage.completionTokens;
      this.activeSession.totalTokens += event.message.usage.totalTokens;
    }
    this.activeSession.cost += cost;
    this.activeSession.updatedAt = now;
    
    // Persist
    this.db.messages.update(message.id, message);
    this.db.sessions.update(this.activeSession.id, {
      promptTokens: this.activeSession.promptTokens,
      completionTokens: this.activeSession.completionTokens,
      totalTokens: this.activeSession.totalTokens,
      cost: this.activeSession.cost,
      updatedAt: now
    });
    
    // Broadcast
    this.store.updateSession(this.activeSession);
    this.broadcast({ 
      type: 'message.completed', 
      message,
      sessionTotals: {
        promptTokens: this.activeSession.promptTokens,
        completionTokens: this.activeSession.completionTokens,
        cost: this.activeSession.cost
      }
    });
  }
  
  // ─── Tool Events ───
  
  handleToolExecuteBefore(event: ToolExecuteBeforeEvent): void {
    if (!this.activeSession) return;
    
    const toolCall: ToolCall = {
      id: event.callId,
      sessionId: this.activeSession.id,
      messageId: event.messageId,
      tool: event.tool,
      category: this.categorize(event.tool),
      startedAt: new Date(),
      completedAt: null,
      duration: null,
      input: event.input,
      output: null,
      status: 'running',
      error: null
    };
    
    this.activeSession.toolCalls.push(toolCall);
    this.db.toolCalls.insert(toolCall);
    
    this.broadcast({ type: 'tool.started', toolCall });
  }
  
  handleToolExecuteAfter(event: ToolExecuteAfterEvent): void {
    if (!this.activeSession) return;
    
    const toolCall = this.activeSession.toolCalls.find(t => t.id === event.callId);
    if (!toolCall) return;
    
    const now = new Date();
    Object.assign(toolCall, {
      completedAt: now,
      duration: now.getTime() - toolCall.startedAt.getTime(),
      output: event.output,
      status: event.error ? 'error' : 'completed',
      error: event.error ?? null
    });
    
    this.db.toolCalls.update(toolCall.id, toolCall);
    
    // Broadcast for flame graph
    this.broadcast({ 
      type: 'tool.completed', 
      toolCall,
      timing: {
        tool: toolCall.tool,
        duration: toolCall.duration,
        success: !toolCall.error
      }
    });
  }
  
  // ─── Helpers ───
  
  private calculateCost(usage: TokenUsage, model: string): number {
    const pricing = MODEL_PRICING[model];
    if (!pricing) return 0;
    
    return (usage.promptTokens / 1_000_000) * pricing.input +
           (usage.completionTokens / 1_000_000) * pricing.output;
  }
  
  private categorize(tool: string): ToolCategory {
    if (tool.startsWith('lean_')) return 'lean';
    if (['read_file', 'write_file', 'list_files'].includes(tool)) return 'file';
    if (['bash', 'exec'].includes(tool)) return 'shell';
    if (['grep', 'find', 'search'].includes(tool)) return 'search';
    return 'mcp';
  }
  
  private broadcast(message: object): void {
    this.store.emit('session.broadcast', message);
  }
}
```

---

## Persistence Schema

### SQLite Tables

```sql
-- sessions table
CREATE TABLE sessions (
  id TEXT PRIMARY KEY,
  name TEXT NOT NULL,
  created_at TEXT NOT NULL,
  updated_at TEXT NOT NULL,
  completed_at TEXT,
  model TEXT NOT NULL,
  provider TEXT NOT NULL,
  prompt_tokens INTEGER NOT NULL DEFAULT 0,
  completion_tokens INTEGER NOT NULL DEFAULT 0,
  total_tokens INTEGER NOT NULL DEFAULT 0,
  cost REAL NOT NULL DEFAULT 0,
  diem_used REAL NOT NULL DEFAULT 0,
  message_count INTEGER NOT NULL DEFAULT 0,
  metadata TEXT, -- JSON
  tags TEXT -- JSON array
);

CREATE INDEX idx_sessions_created ON sessions(created_at DESC);
CREATE INDEX idx_sessions_model ON sessions(model);

-- messages table  
CREATE TABLE messages (
  id TEXT PRIMARY KEY,
  session_id TEXT NOT NULL REFERENCES sessions(id),
  role TEXT NOT NULL,
  content TEXT NOT NULL,
  created_at TEXT NOT NULL,
  completed_at TEXT,
  duration INTEGER,
  status TEXT NOT NULL,
  error TEXT, -- JSON
  usage TEXT, -- JSON
  cost REAL NOT NULL DEFAULT 0
);

CREATE INDEX idx_messages_session ON messages(session_id);
CREATE INDEX idx_messages_created ON messages(created_at);

-- tool_calls table
CREATE TABLE tool_calls (
  id TEXT PRIMARY KEY,
  session_id TEXT NOT NULL REFERENCES sessions(id),
  message_id TEXT NOT NULL REFERENCES messages(id),
  tool TEXT NOT NULL,
  category TEXT NOT NULL,
  started_at TEXT NOT NULL,
  completed_at TEXT,
  duration INTEGER,
  input TEXT NOT NULL, -- JSON
  output TEXT, -- JSON
  status TEXT NOT NULL,
  error TEXT
);

CREATE INDEX idx_tool_calls_session ON tool_calls(session_id);
CREATE INDEX idx_tool_calls_tool ON tool_calls(tool);
CREATE INDEX idx_tool_calls_duration ON tool_calls(duration);
```

---

## WebSocket Broadcasts

### Session Updates

```typescript
// session.created
{
  jsonrpc: '2.0',
  method: 'session.created',
  params: {
    id: 'sess_abc123',
    name: 'Refactor auth module',
    model: 'llama-3.3-70b',
    createdAt: '2026-01-16T10:30:00Z'
  }
}

// session.update (periodic or on significant change)
{
  jsonrpc: '2.0',
  method: 'session.update',
  params: {
    id: 'sess_abc123',
    promptTokens: 15234,
    completionTokens: 8721,
    totalTokens: 23955,
    cost: 0.0143,
    messageCount: 12,
    updatedAt: '2026-01-16T10:45:00Z'
  }
}

// usage.update (per message)
{
  jsonrpc: '2.0',
  method: 'usage.update',
  params: {
    messageId: 'msg_xyz789',
    sessionId: 'sess_abc123',
    promptTokens: 1234,
    completionTokens: 567,
    cost: 0.0012,
    model: 'llama-3.3-70b',
    duration: 2345,
    timestamp: '2026-01-16T10:46:00Z'
  }
}

// tool.timing (for flame graph)
{
  jsonrpc: '2.0',
  method: 'tool.timing',
  params: {
    tool: 'read_file',
    duration: 45,
    success: true,
    timestamp: '2026-01-16T10:46:01Z'
  }
}
```

---

## PureScript Session State

```purescript
module Sidepanel.State.Session where

import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Data.Array (Array)

type SessionState =
  { current :: Maybe ActiveSession
  , history :: Array SessionSummary
  , isLoading :: Boolean
  }

type ActiveSession =
  { id :: String
  , name :: String
  , model :: String
  , promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cost :: Number
  , messageCount :: Int
  , startedAt :: DateTime
  , updatedAt :: DateTime
  , recentMessages :: Array MessageSummary
  }

type SessionSummary =
  { id :: String
  , name :: String
  , model :: String
  , totalTokens :: Int
  , cost :: Number
  , messageCount :: Int
  , createdAt :: DateTime
  , duration :: Int -- minutes
  }

type MessageSummary =
  { id :: String
  , role :: Role
  , preview :: String  -- First 100 chars
  , tokens :: Int
  , cost :: Number
  , createdAt :: DateTime
  }

data Role = User | Assistant | System | Tool
```

---

## Session Export

Users can export session data for analysis or archival.

### Export Formats

**JSON (Full)**
```json
{
  "session": {
    "id": "sess_abc123",
    "name": "Refactor auth module",
    "model": "llama-3.3-70b",
    ...
  },
  "messages": [...],
  "toolCalls": [...],
  "exportedAt": "2026-01-16T12:00:00Z"
}
```

**Markdown (Readable)**
```markdown
# Session: Refactor auth module

**Model:** llama-3.3-70b  
**Duration:** 45 minutes  
**Tokens:** 23,955 (15,234 in / 8,721 out)  
**Cost:** $0.0143

---

## Conversation

**User:** Can you help me refactor the authentication module?

**Assistant:** I'd be happy to help! Let me first look at the current implementation...

[continues...]
```

---

## Related Specifications

- `21-PLUGIN-SYSTEM.md` - Event sources
- `24-MESSAGE-FLOW.md` - Message lifecycle details
- `25-TOOL-EXECUTION.md` - Tool tracking
- `36-SESSION-PERSISTENCE.md` - Storage details
- `54-SESSION-HISTORY-PANEL.md` - UI component

---

*"What gets measured gets managed. What gets persisted can be time-traveled."*
