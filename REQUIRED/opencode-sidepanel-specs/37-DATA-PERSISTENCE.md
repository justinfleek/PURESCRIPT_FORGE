# 37-DATA-PERSISTENCE: Storage Strategy and State Recovery

## Overview

This document defines how data is persisted across sessions, including localStorage for settings, SQLite for historical data, and state recovery mechanisms.

---

## Storage Layers

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           STORAGE ARCHITECTURE                              │
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                        RUNTIME STATE (Memory)                        │   │
│  │   Current session, UI state, real-time metrics, WebSocket state     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    │                                        │
│                                    ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                     LOCAL STORAGE (Browser)                          │   │
│  │   Settings, preferences, UI state, recent items, auth tokens        │   │
│  │   ~5MB limit, synchronous, survives refresh                         │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    │                                        │
│                                    ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                       SQLITE (Bridge Server)                         │   │
│  │   Sessions, messages, snapshots, recordings, analytics              │   │
│  │   Unlimited size, indexed queries, full history                     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## What Goes Where

### LocalStorage (Browser)

| Key | Data | Purpose |
|-----|------|---------|
| `sidepanel.settings` | JSON | User preferences |
| `sidepanel.theme` | string | Theme selection |
| `sidepanel.ui.sidebarCollapsed` | boolean | UI state |
| `sidepanel.ui.lastView` | string | Last active view |
| `sidepanel.recent.sessions` | string[] | Recent session IDs |
| `sidepanel.recent.searches` | string[] | Search history |
| `sidepanel.auth.token` | string | API token |
| `sidepanel.tour.completed` | boolean | Onboarding state |
| `sidepanel.help.dismissed` | string[] | Dismissed help items |

### SQLite (Bridge)

| Table | Data | Retention |
|-------|------|-----------|
| `sessions` | Session metadata | Forever (user-deleted) |
| `messages` | Message content | Forever (session-deleted) |
| `snapshots` | State snapshots | 30 days (non-starred) |
| `recordings` | Session recordings | Forever (user-deleted) |
| `analytics` | Usage metrics | 90 days |
| `file_changes` | Diff history | Session lifetime |
| `proofs` | Proof states | Session lifetime |

---

## LocalStorage Schema

```typescript
interface LocalStorageSchema {
  // Settings
  'sidepanel.settings': {
    version: number;
    defaultModel: string;
    notifications: NotificationSettings;
    keyboard: KeyboardSettings;
  };
  
  // Theme
  'sidepanel.theme': 'dark' | 'light' | 'system';
  
  // UI State
  'sidepanel.ui': {
    sidebarCollapsed: boolean;
    lastView: string;
    panelSizes: Record<string, number>;
  };
  
  // Recent Items
  'sidepanel.recent.sessions': string[];
  'sidepanel.recent.searches': string[];
  'sidepanel.recent.commands': string[];
  
  // Auth
  'sidepanel.auth.token': string;
  
  // Onboarding
  'sidepanel.tour.completed': boolean;
  'sidepanel.help.dismissed': string[];
  
  // Debug
  'sidepanel.debug.enabled': boolean;
}
```

### LocalStorage Service

```typescript
// frontend/src/services/localStorage.ts

class LocalStorageService {
  private prefix = 'sidepanel';
  
  private key(name: string): string {
    return `${this.prefix}.${name}`;
  }
  
  get<T>(name: string, defaultValue?: T): T | null {
    try {
      const item = localStorage.getItem(this.key(name));
      return item ? JSON.parse(item) : (defaultValue ?? null);
    } catch {
      return defaultValue ?? null;
    }
  }
  
  set<T>(name: string, value: T): void {
    try {
      localStorage.setItem(this.key(name), JSON.stringify(value));
    } catch (error) {
      console.error('LocalStorage write failed:', error);
      // Handle quota exceeded
      if (error.name === 'QuotaExceededError') {
        this.cleanup();
        localStorage.setItem(this.key(name), JSON.stringify(value));
      }
    }
  }
  
  remove(name: string): void {
    localStorage.removeItem(this.key(name));
  }
  
  // Clean old data when quota exceeded
  private cleanup(): void {
    // Remove old search history
    const searches = this.get<string[]>('recent.searches', []);
    this.set('recent.searches', searches.slice(0, 10));
    
    // Remove old commands
    const commands = this.get<string[]>('recent.commands', []);
    this.set('recent.commands', commands.slice(0, 10));
  }
  
  // Export all settings for backup
  exportAll(): Record<string, any> {
    const data: Record<string, any> = {};
    for (let i = 0; i < localStorage.length; i++) {
      const key = localStorage.key(i);
      if (key?.startsWith(this.prefix)) {
        data[key] = this.get(key.replace(this.prefix + '.', ''));
      }
    }
    return data;
  }
  
  // Import settings from backup
  importAll(data: Record<string, any>): void {
    for (const [key, value] of Object.entries(data)) {
      if (key.startsWith(this.prefix)) {
        this.set(key.replace(this.prefix + '.', ''), value);
      }
    }
  }
}

export const storage = new LocalStorageService();
```

---

## SQLite Schema

```sql
-- Sessions table
CREATE TABLE IF NOT EXISTS sessions (
  id TEXT PRIMARY KEY,
  title TEXT NOT NULL,
  created_at TEXT NOT NULL,
  updated_at TEXT NOT NULL,
  model TEXT NOT NULL,
  provider TEXT DEFAULT 'venice',
  
  -- Branch info
  branch_name TEXT DEFAULT 'main',
  parent_session_id TEXT REFERENCES sessions(id),
  branch_point INTEGER,
  
  -- Metrics
  prompt_tokens INTEGER DEFAULT 0,
  completion_tokens INTEGER DEFAULT 0,
  cost REAL DEFAULT 0,
  
  -- State
  is_archived INTEGER DEFAULT 0,
  is_imported INTEGER DEFAULT 0,
  
  -- Indexes
  FOREIGN KEY (parent_session_id) REFERENCES sessions(id)
);

CREATE INDEX idx_sessions_updated ON sessions(updated_at DESC);
CREATE INDEX idx_sessions_archived ON sessions(is_archived);

-- Messages table
CREATE TABLE IF NOT EXISTS messages (
  id TEXT PRIMARY KEY,
  session_id TEXT NOT NULL REFERENCES sessions(id) ON DELETE CASCADE,
  role TEXT NOT NULL,
  content TEXT NOT NULL,
  created_at TEXT NOT NULL,
  
  -- Metrics
  prompt_tokens INTEGER,
  completion_tokens INTEGER,
  
  -- Tool calls
  tool_calls TEXT,  -- JSON array
  
  -- Ordering
  sequence INTEGER NOT NULL,
  
  FOREIGN KEY (session_id) REFERENCES sessions(id)
);

CREATE INDEX idx_messages_session ON messages(session_id, sequence);

-- Snapshots table
CREATE TABLE IF NOT EXISTS snapshots (
  id TEXT PRIMARY KEY,
  timestamp TEXT NOT NULL,
  type TEXT NOT NULL,  -- 'auto', 'manual', 'system'
  trigger TEXT NOT NULL,  -- JSON
  description TEXT,
  starred INTEGER DEFAULT 0,
  size_bytes INTEGER NOT NULL,
  state_json TEXT NOT NULL,
  summary_json TEXT NOT NULL
);

CREATE INDEX idx_snapshots_timestamp ON snapshots(timestamp DESC);
CREATE INDEX idx_snapshots_starred ON snapshots(starred);

-- Recordings table
CREATE TABLE IF NOT EXISTS recordings (
  id TEXT PRIMARY KEY,
  session_id TEXT NOT NULL,
  title TEXT NOT NULL,
  created_at TEXT NOT NULL,
  duration INTEGER NOT NULL,
  events_json TEXT NOT NULL,
  snapshots_json TEXT,
  metadata_json TEXT
);

CREATE INDEX idx_recordings_session ON recordings(session_id);

-- Analytics table
CREATE TABLE IF NOT EXISTS analytics (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  timestamp TEXT NOT NULL,
  event_type TEXT NOT NULL,
  session_id TEXT,
  model TEXT,
  prompt_tokens INTEGER,
  completion_tokens INTEGER,
  cost REAL,
  duration_ms INTEGER,
  metadata_json TEXT
);

CREATE INDEX idx_analytics_timestamp ON analytics(timestamp DESC);
CREATE INDEX idx_analytics_session ON analytics(session_id);
```

---

## State Recovery

### On App Start

```typescript
// bridge/src/state/recovery.ts

export class StateRecovery {
  async initialize(): Promise<AppState> {
    // 1. Load settings from localStorage (browser)
    const settings = await this.loadSettings();
    
    // 2. Check for crash recovery
    const crashState = await this.checkCrashState();
    if (crashState) {
      return this.promptRecovery(crashState);
    }
    
    // 3. Load last session from SQLite
    const lastSession = await this.loadLastSession();
    
    // 4. Fetch current balance from Venice
    const balance = await this.fetchBalance();
    
    // 5. Restore UI state
    const uiState = await this.loadUIState();
    
    return {
      settings,
      session: lastSession,
      balance,
      ui: uiState
    };
  }
  
  private async checkCrashState(): Promise<CrashState | null> {
    // Check for incomplete session in localStorage
    const crashData = storage.get<CrashState>('crash.recovery');
    
    if (crashData && this.isRecent(crashData.timestamp)) {
      return crashData;
    }
    
    // Clean up old crash data
    storage.remove('crash.recovery');
    return null;
  }
  
  private isRecent(timestamp: string): boolean {
    const crashTime = new Date(timestamp).getTime();
    const now = Date.now();
    const maxAge = 30 * 60 * 1000;  // 30 minutes
    return now - crashTime < maxAge;
  }
  
  private async promptRecovery(state: CrashState): Promise<AppState> {
    // Notify UI to show recovery prompt
    this.emit('recovery.available', {
      sessionTitle: state.session?.title,
      messageCount: state.session?.messages?.length,
      timestamp: state.timestamp
    });
    
    // Wait for user decision
    const decision = await this.waitForDecision();
    
    if (decision === 'restore') {
      // Restore crash state
      await this.restoreCrashState(state);
    }
    
    // Clear crash data
    storage.remove('crash.recovery');
    
    return this.buildState(decision === 'restore' ? state : null);
  }
}
```

### Periodic Backup

```typescript
// Auto-save state every 30 seconds
class AutoSave {
  private interval: NodeJS.Timer | null = null;
  private lastState: string = '';
  
  start(store: Store): void {
    this.interval = setInterval(() => {
      this.save(store.getState());
    }, 30000);
    
    // Also save on state changes (debounced)
    store.subscribe(debounce(() => {
      this.save(store.getState());
    }, 5000));
    
    // Save on window close
    window.addEventListener('beforeunload', () => {
      this.save(store.getState());
    });
  }
  
  private save(state: AppState): void {
    const serialized = JSON.stringify({
      timestamp: new Date().toISOString(),
      session: state.session,
      balance: state.balance,
      ui: {
        currentView: state.ui.currentView,
        sidebarCollapsed: state.ui.sidebarCollapsed
      }
    });
    
    // Only save if changed
    if (serialized !== this.lastState) {
      storage.set('crash.recovery', JSON.parse(serialized));
      this.lastState = serialized;
    }
  }
  
  stop(): void {
    if (this.interval) {
      clearInterval(this.interval);
      this.interval = null;
    }
    storage.remove('crash.recovery');
  }
}
```

---

## Data Migration

### Version Tracking

```typescript
const SCHEMA_VERSION = 3;

async function migrateIfNeeded(db: Database): Promise<void> {
  const currentVersion = await db.get('SELECT version FROM schema_version');
  
  if (!currentVersion) {
    // Fresh install
    await runMigrations(db, 0, SCHEMA_VERSION);
  } else if (currentVersion.version < SCHEMA_VERSION) {
    // Upgrade needed
    await runMigrations(db, currentVersion.version, SCHEMA_VERSION);
  }
  
  await db.run('INSERT OR REPLACE INTO schema_version (id, version) VALUES (1, ?)', [SCHEMA_VERSION]);
}

async function runMigrations(db: Database, from: number, to: number): Promise<void> {
  for (let v = from + 1; v <= to; v++) {
    const migration = migrations[v];
    if (migration) {
      console.log(`Running migration v${v}`);
      await migration(db);
    }
  }
}

const migrations: Record<number, (db: Database) => Promise<void>> = {
  1: async (db) => {
    // v1: Initial schema
    await db.exec(INITIAL_SCHEMA);
  },
  2: async (db) => {
    // v2: Add branch support
    await db.exec(`
      ALTER TABLE sessions ADD COLUMN branch_name TEXT DEFAULT 'main';
      ALTER TABLE sessions ADD COLUMN parent_session_id TEXT;
      ALTER TABLE sessions ADD COLUMN branch_point INTEGER;
    `);
  },
  3: async (db) => {
    // v3: Add analytics
    await db.exec(`
      CREATE TABLE IF NOT EXISTS analytics (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        timestamp TEXT NOT NULL,
        event_type TEXT NOT NULL,
        ...
      );
    `);
  }
};
```

---

## Data Cleanup

### Automatic Cleanup

```typescript
// Run nightly
async function cleanupOldData(db: Database): Promise<void> {
  const now = new Date();
  
  // Delete non-starred snapshots older than 30 days
  const snapshotCutoff = new Date(now.getTime() - 30 * 24 * 60 * 60 * 1000);
  await db.run(`
    DELETE FROM snapshots 
    WHERE starred = 0 AND timestamp < ?
  `, [snapshotCutoff.toISOString()]);
  
  // Delete analytics older than 90 days
  const analyticsCutoff = new Date(now.getTime() - 90 * 24 * 60 * 60 * 1000);
  await db.run(`
    DELETE FROM analytics WHERE timestamp < ?
  `, [analyticsCutoff.toISOString()]);
  
  // Vacuum to reclaim space
  await db.run('VACUUM');
}
```

---

## Related Specifications

- `34-DATABASE-SCHEMA.md` - Full schema details
- `64-SNAPSHOT-MANAGEMENT.md` - Snapshot storage
- `41-STATE-MANAGEMENT.md` - Runtime state

---

*"Data persists. State recovers. Nothing is lost."*
