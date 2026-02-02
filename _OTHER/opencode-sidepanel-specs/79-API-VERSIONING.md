# 79-API-VERSIONING: Version Management and Compatibility

## Overview

API versioning ensures backward compatibility and smooth upgrades across sidepanel components. This document covers versioning strategies for WebSocket protocol, data schemas, and plugin APIs.

---

## Version Scheme

### Semantic Versioning

```
MAJOR.MINOR.PATCH

MAJOR - Breaking changes
MINOR - New features (backward compatible)
PATCH - Bug fixes (backward compatible)
```

### Component Versions

| Component | Current | Protocol |
|-----------|---------|----------|
| Bridge Server | 0.1.0 | 1 |
| Frontend | 0.1.0 | 1 |
| Plugin API | 0.1.0 | 1 |
| Data Schema | 1 | - |

---

## Protocol Versioning

### WebSocket Protocol

```typescript
// Client announces version on connect
interface ConnectMessage {
  jsonrpc: '2.0';
  method: 'connect';
  params: {
    protocolVersion: number;  // e.g., 1
    clientVersion: string;    // e.g., "0.1.0"
    capabilities: string[];   // e.g., ["streaming", "tools"]
  };
}

// Server responds with negotiated version
interface ConnectResponse {
  jsonrpc: '2.0';
  result: {
    protocolVersion: number;  // Negotiated version
    serverVersion: string;
    capabilities: string[];
  };
}
```

### Version Negotiation

```typescript
// bridge/src/versioning/negotiate.ts

const SUPPORTED_VERSIONS = [1];
const CURRENT_VERSION = 1;

function negotiateVersion(clientVersion: number): number {
  if (SUPPORTED_VERSIONS.includes(clientVersion)) {
    return clientVersion;
  }
  
  // Find highest compatible version
  const compatible = SUPPORTED_VERSIONS
    .filter(v => v <= clientVersion)
    .sort((a, b) => b - a)[0];
  
  if (!compatible) {
    throw new Error(`Unsupported protocol version: ${clientVersion}`);
  }
  
  return compatible;
}
```

---

## Schema Versioning

### Database Migrations

```typescript
// bridge/src/db/migrations/index.ts

interface Migration {
  version: number;
  up: (db: Database) => Promise<void>;
  down: (db: Database) => Promise<void>;
}

const migrations: Migration[] = [
  {
    version: 1,
    up: async (db) => {
      // Initial schema
      await db.exec(`
        CREATE TABLE sessions (...);
        CREATE TABLE messages (...);
      `);
    },
    down: async (db) => {
      await db.exec('DROP TABLE messages; DROP TABLE sessions;');
    }
  },
  {
    version: 2,
    up: async (db) => {
      // Add branching support
      await db.exec(`
        ALTER TABLE sessions ADD COLUMN branch_name TEXT DEFAULT 'main';
        ALTER TABLE sessions ADD COLUMN parent_session_id TEXT;
      `);
    },
    down: async (db) => {
      // SQLite doesn't support DROP COLUMN easily
      // Would need table recreation
    }
  },
  {
    version: 3,
    up: async (db) => {
      // Add analytics
      await db.exec('CREATE TABLE analytics (...)');
    },
    down: async (db) => {
      await db.exec('DROP TABLE analytics');
    }
  }
];

async function migrate(db: Database): Promise<void> {
  const currentVersion = await getCurrentVersion(db);
  
  for (const migration of migrations) {
    if (migration.version > currentVersion) {
      console.log(`Applying migration v${migration.version}`);
      await migration.up(db);
      await setVersion(db, migration.version);
    }
  }
}
```

### Export/Import Versioning

```typescript
interface ExportedData {
  version: number;       // Schema version
  exportedAt: string;
  data: unknown;         // Version-specific structure
}

// Import with version handling
async function importData(exported: ExportedData): Promise<void> {
  const currentVersion = getCurrentSchemaVersion();
  
  if (exported.version > currentVersion) {
    throw new Error('Export is from newer version. Please upgrade.');
  }
  
  // Migrate data if from older version
  let data = exported.data;
  for (let v = exported.version; v < currentVersion; v++) {
    data = await migrateExport(data, v, v + 1);
  }
  
  await importMigratedData(data);
}
```

---

## Plugin API Versioning

### Plugin Manifest

```json
{
  "name": "my-plugin",
  "version": "1.0.0",
  "opencode": {
    "minVersion": "0.5.0",
    "maxVersion": "1.x",
    "apiVersion": 1
  }
}
```

### API Version Compatibility

```typescript
// bridge/src/plugins/compatibility.ts

const API_VERSIONS = {
  1: {
    events: ['session.created', 'message.created', 'balance.update'],
    methods: ['getSession', 'sendMessage', 'getBalance']
  },
  2: {
    events: [...API_VERSIONS[1].events, 'snapshot.created', 'branch.created'],
    methods: [...API_VERSIONS[1].methods, 'createSnapshot', 'createBranch']
  }
};

function getApiForVersion(version: number): PluginApi {
  const spec = API_VERSIONS[version];
  if (!spec) {
    throw new Error(`Unsupported API version: ${version}`);
  }
  
  return createRestrictedApi(spec);
}
```

---

## Deprecation Policy

### Timeline

```
Announcement → +6 months → Deprecated → +6 months → Removed

Example:
v1.0: Feature X announced as deprecated
v1.6: Feature X shows warnings in logs
v2.0: Feature X removed
```

### Deprecation Warnings

```typescript
// Deprecation decorator
function deprecated(message: string, removeIn: string) {
  return function(target: any, key: string, descriptor: PropertyDescriptor) {
    const original = descriptor.value;
    
    descriptor.value = function(...args: any[]) {
      console.warn(
        `[DEPRECATED] ${key}: ${message}. Will be removed in ${removeIn}.`
      );
      return original.apply(this, args);
    };
    
    return descriptor;
  };
}

class SessionManager {
  @deprecated('Use getSessionById instead', 'v2.0')
  getSession(id: string): Session {
    return this.getSessionById(id);
  }
  
  getSessionById(id: string): Session {
    // New implementation
  }
}
```

---

## Compatibility Matrix

### Frontend ↔ Bridge Compatibility

| Frontend | Bridge 0.1.x | Bridge 0.2.x | Bridge 1.0.x |
|----------|--------------|--------------|--------------|
| 0.1.x | ✅ | ✅ | ⚠️ |
| 0.2.x | ⚠️ | ✅ | ✅ |
| 1.0.x | ❌ | ⚠️ | ✅ |

✅ Full compatibility
⚠️ Compatible with warnings
❌ Not compatible

### Breaking Changes Log

```markdown
## v1.0.0 (Future)
- WebSocket protocol v2 required
- Session schema v3 required
- Removed deprecated `getSession` method

## v0.2.0
- Added session branching (protocol v1 compatible)
- New analytics schema (migration required)
- Deprecated `getSession` in favor of `getSessionById`

## v0.1.0
- Initial release
- Protocol v1
- Schema v1
```

---

## Version Detection

### Runtime Version Check

```typescript
// bridge/src/versioning/check.ts

interface VersionInfo {
  bridge: string;
  protocol: number;
  schema: number;
  nodeVersion: string;
}

function getVersionInfo(): VersionInfo {
  return {
    bridge: process.env.VERSION ?? '0.1.0',
    protocol: PROTOCOL_VERSION,
    schema: SCHEMA_VERSION,
    nodeVersion: process.version
  };
}

// Expose via API
app.get('/version', (req, res) => {
  res.json(getVersionInfo());
});
```

### Client Version Check

```typescript
// On connect, verify compatibility
async function checkCompatibility(): Promise<void> {
  const serverVersion = await fetch('/version').then(r => r.json());
  const clientVersion = getClientVersion();
  
  if (serverVersion.protocol !== clientVersion.protocol) {
    if (serverVersion.protocol > clientVersion.protocol) {
      showUpgradeNotice('Please refresh to get the latest version.');
    } else {
      showWarning('Server is older than client. Some features may not work.');
    }
  }
}
```

---

## Related Specifications

- `31-WEBSOCKET-PROTOCOL.md` - Protocol details
- `34-DATABASE-SCHEMA.md` - Schema structure
- `21-PLUGIN-SYSTEM.md` - Plugin API

---

*"Good versioning means never saying 'it worked yesterday'."*
