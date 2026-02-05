# 78-BACKUP-RECOVERY: Data Backup and Disaster Recovery

## Overview

Backup and recovery procedures ensure data durability and business continuity. This document covers backup strategies, recovery procedures, and data retention policies.

---

## Data Categories

| Category | Criticality | Backup Frequency | Retention |
|----------|-------------|------------------|-----------|
| Sessions | High | Continuous | Forever |
| Messages | High | Continuous | Forever |
| Settings | Medium | On change | 30 days |
| Analytics | Low | Daily | 90 days |
| Logs | Low | Daily | 7 days |
| Snapshots | Medium | On creation | 30 days |

---

## Backup Strategies

### 1. SQLite Database Backup

```bash
#!/bin/bash
# backup/backup-db.sh

BACKUP_DIR="/var/backups/sidepanel"
DB_PATH="/var/lib/sidepanel/sidepanel.db"
DATE=$(date +%Y%m%d_%H%M%S)
BACKUP_FILE="$BACKUP_DIR/sidepanel_$DATE.db"

# Create backup directory
mkdir -p "$BACKUP_DIR"

# Use SQLite backup command (safe for live database)
sqlite3 "$DB_PATH" ".backup '$BACKUP_FILE'"

# Compress
gzip "$BACKUP_FILE"

# Verify
if [ -f "$BACKUP_FILE.gz" ]; then
    echo "Backup successful: $BACKUP_FILE.gz"
    echo "Size: $(du -h "$BACKUP_FILE.gz" | cut -f1)"
else
    echo "Backup failed!"
    exit 1
fi

# Clean old backups (keep last 7 days)
find "$BACKUP_DIR" -name "*.db.gz" -mtime +7 -delete
```

### 2. Settings Export

```typescript
// bridge/src/backup/settings.ts

export async function exportSettings(): Promise<SettingsBackup> {
  const db = getDatabase();
  
  return {
    version: '1.0',
    exportedAt: new Date().toISOString(),
    settings: {
      theme: await db.get('SELECT * FROM settings WHERE key = "theme"'),
      keyboard: await db.get('SELECT * FROM settings WHERE key = "keyboard"'),
      notifications: await db.get('SELECT * FROM settings WHERE key = "notifications"'),
      models: await db.get('SELECT * FROM settings WHERE key = "models"')
    },
    customPrompts: await db.all('SELECT * FROM custom_prompts'),
    favoriteActions: await db.all('SELECT * FROM favorite_actions')
  };
}

export async function importSettings(backup: SettingsBackup): Promise<void> {
  const db = getDatabase();
  
  await db.run('BEGIN TRANSACTION');
  
  try {
    // Restore settings
    for (const [key, value] of Object.entries(backup.settings)) {
      await db.run(
        'INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)',
        [key, JSON.stringify(value)]
      );
    }
    
    // Restore custom prompts
    for (const prompt of backup.customPrompts) {
      await db.run(
        'INSERT OR REPLACE INTO custom_prompts (id, name, template) VALUES (?, ?, ?)',
        [prompt.id, prompt.name, prompt.template]
      );
    }
    
    await db.run('COMMIT');
  } catch (error) {
    await db.run('ROLLBACK');
    throw error;
  }
}
```

### 3. Session Archive

```typescript
// bridge/src/backup/sessions.ts

export async function archiveSession(sessionId: string): Promise<string> {
  const db = getDatabase();
  
  // Get session with all messages
  const session = await db.get('SELECT * FROM sessions WHERE id = ?', [sessionId]);
  const messages = await db.all(
    'SELECT * FROM messages WHERE session_id = ? ORDER BY sequence',
    [sessionId]
  );
  
  const archive: SessionArchive = {
    version: '1.0',
    archivedAt: new Date().toISOString(),
    session,
    messages,
    metadata: {
      messageCount: messages.length,
      tokenCount: messages.reduce((sum, m) => sum + (m.tokens_total || 0), 0),
      duration: calculateDuration(session, messages)
    }
  };
  
  // Save to archive location
  const archivePath = path.join(
    ARCHIVE_DIR,
    `session_${sessionId}_${Date.now()}.json.gz`
  );
  
  await fs.writeFile(
    archivePath,
    gzipSync(JSON.stringify(archive))
  );
  
  return archivePath;
}

export async function restoreSession(archivePath: string): Promise<string> {
  const compressed = await fs.readFile(archivePath);
  const archive: SessionArchive = JSON.parse(gunzipSync(compressed).toString());
  
  const db = getDatabase();
  
  // Generate new ID to avoid conflicts
  const newSessionId = generateId();
  
  await db.run('BEGIN TRANSACTION');
  
  try {
    // Insert session with new ID
    await db.run(
      `INSERT INTO sessions (id, title, created_at, updated_at, model, prompt_tokens, completion_tokens, cost)
       VALUES (?, ?, ?, ?, ?, ?, ?, ?)`,
      [
        newSessionId,
        archive.session.title + ' (restored)',
        archive.session.created_at,
        new Date().toISOString(),
        archive.session.model,
        archive.session.prompt_tokens,
        archive.session.completion_tokens,
        archive.session.cost
      ]
    );
    
    // Insert messages
    for (const msg of archive.messages) {
      await db.run(
        `INSERT INTO messages (id, session_id, sequence, role, content, timestamp)
         VALUES (?, ?, ?, ?, ?, ?)`,
        [generateId(), newSessionId, msg.sequence, msg.role, msg.content, msg.timestamp]
      );
    }
    
    await db.run('COMMIT');
    return newSessionId;
  } catch (error) {
    await db.run('ROLLBACK');
    throw error;
  }
}
```

---

## Automated Backup Schedule

```yaml
# docker-compose.yml backup service
services:
  backup:
    image: sidepanel-backup
    volumes:
      - ./data:/data:ro
      - ./backups:/backups
    environment:
      - BACKUP_SCHEDULE=0 */6 * * *  # Every 6 hours
      - RETENTION_DAYS=7
      - S3_BUCKET=sidepanel-backups
    command: ["crond", "-f"]
```

```bash
# crontab for backup service
# Daily full backup at 2am
0 2 * * * /scripts/backup-full.sh

# Incremental backup every 6 hours
0 */6 * * * /scripts/backup-incremental.sh

# Weekly archive cleanup
0 3 * * 0 /scripts/cleanup-old-backups.sh
```

---

## Recovery Procedures

### 1. Database Recovery

```bash
#!/bin/bash
# backup/restore-db.sh

BACKUP_FILE=$1
DB_PATH="/var/lib/sidepanel/sidepanel.db"

if [ -z "$BACKUP_FILE" ]; then
    echo "Usage: restore-db.sh <backup-file.db.gz>"
    exit 1
fi

# Stop service
systemctl stop sidepanel

# Backup current (in case restore fails)
cp "$DB_PATH" "$DB_PATH.pre-restore"

# Decompress and restore
gunzip -c "$BACKUP_FILE" > "$DB_PATH"

# Verify integrity
if sqlite3 "$DB_PATH" "PRAGMA integrity_check;" | grep -q "ok"; then
    echo "Database restored successfully"
    systemctl start sidepanel
else
    echo "Database integrity check failed, rolling back"
    mv "$DB_PATH.pre-restore" "$DB_PATH"
    systemctl start sidepanel
    exit 1
fi
```

### 2. Point-in-Time Recovery

```typescript
export async function recoverToPoint(timestamp: Date): Promise<void> {
  // Find closest backup before timestamp
  const backups = await listBackups();
  const targetBackup = backups
    .filter(b => b.timestamp < timestamp)
    .sort((a, b) => b.timestamp - a.timestamp)[0];
  
  if (!targetBackup) {
    throw new Error('No backup found before specified timestamp');
  }
  
  // Restore base backup
  await restoreBackup(targetBackup.path);
  
  // Apply transaction log up to timestamp
  const transactions = await getTransactionLog(targetBackup.timestamp, timestamp);
  for (const tx of transactions) {
    await applyTransaction(tx);
  }
}
```

### 3. Disaster Recovery Checklist

```markdown
## Disaster Recovery Checklist

### Immediate Actions (< 1 hour)
- [ ] Assess scope of data loss
- [ ] Notify stakeholders
- [ ] Identify most recent clean backup
- [ ] Document timeline of events

### Recovery Actions (1-4 hours)
- [ ] Stop affected services
- [ ] Restore database from backup
- [ ] Verify data integrity
- [ ] Test basic functionality
- [ ] Restore settings and configuration

### Post-Recovery (< 24 hours)
- [ ] Full system verification
- [ ] User communication
- [ ] Incident documentation
- [ ] Root cause analysis
- [ ] Update backup procedures if needed
```

---

## Data Retention Policy

```typescript
interface RetentionPolicy {
  sessions: 'forever';           // User data never deleted automatically
  messages: 'forever';           // Part of sessions
  snapshots: {
    starred: 'forever';          // User-starred snapshots kept
    auto: '30d';                 // Auto snapshots expire
  };
  recordings: 'forever';         // User explicitly created
  analytics: '90d';              // Aggregated metrics
  logs: '7d';                    // Operational logs
  backups: {
    daily: '7d';
    weekly: '30d';
    monthly: '1y';
  };
}

// Cleanup job
async function enforceRetention(): Promise<void> {
  const db = getDatabase();
  const now = new Date();
  
  // Clean auto snapshots older than 30 days
  await db.run(`
    DELETE FROM snapshots 
    WHERE starred = 0 
    AND timestamp < datetime('now', '-30 days')
  `);
  
  // Clean analytics older than 90 days
  await db.run(`
    DELETE FROM analytics 
    WHERE timestamp < datetime('now', '-90 days')
  `);
  
  // Vacuum to reclaim space
  await db.run('VACUUM');
}
```

---

## Related Specifications

- `34-DATABASE-SCHEMA.md` - Database structure
- `37-DATA-PERSISTENCE.md` - Storage strategy
- `86-EXPORT-FUNCTIONALITY.md` - Export features

---

*"Hope for the best, prepare for the worst. Always have backups."*
