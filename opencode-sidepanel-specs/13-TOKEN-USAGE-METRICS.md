# 13-TOKEN-USAGE-METRICS: Collection and Aggregation

## Overview

Token usage metrics track consumption across sessions, models, and time periods. This data powers the dashboard charts, cost projections, and usage alerts.

---

## Metric Types

### Per-Message Metrics

Captured with every AI response:

```typescript
interface MessageMetrics {
  messageId: string;
  sessionId: string;
  timestamp: Date;
  model: string;
  provider: string;
  
  // Token counts
  promptTokens: number;
  completionTokens: number;
  cachedTokens: number;  // Venice-specific
  totalTokens: number;
  
  // Cost
  cost: number;          // In USD
  diemCost: number;      // If paid from Diem
  
  // Timing
  latencyMs: number;     // Time to first token
  durationMs: number;    // Total response time
  tokensPerSecond: number;
}
```

### Per-Session Metrics

Aggregated from messages:

```typescript
interface SessionMetrics {
  sessionId: string;
  startedAt: Date;
  lastActivityAt: Date;
  
  // Totals
  messageCount: number;
  totalPromptTokens: number;
  totalCompletionTokens: number;
  totalTokens: number;
  totalCost: number;
  
  // Averages
  avgTokensPerMessage: number;
  avgLatencyMs: number;
  
  // By model (for multi-model sessions)
  byModel: Record<string, ModelUsage>;
}

interface ModelUsage {
  model: string;
  messageCount: number;
  promptTokens: number;
  completionTokens: number;
  cost: number;
}
```

### Time-Aggregated Metrics

For charts and trends:

```typescript
interface TimeSeriesPoint {
  timestamp: Date;       // Bucket start time
  bucketSize: 'minute' | 'hour' | 'day';
  
  promptTokens: number;
  completionTokens: number;
  totalCost: number;
  messageCount: number;
  sessionCount: number;
}
```

---

## Collection

### From Plugin Events

```typescript
// bridge/src/metrics/collector.ts

class MetricsCollector {
  private db: Database;
  
  constructor(db: Database) {
    this.db = db;
  }
  
  // Called when message.completed event fires
  recordMessage(message: Message, session: Session): void {
    if (!message.usage) return;
    
    const metrics: MessageMetrics = {
      messageId: message.id,
      sessionId: session.id,
      timestamp: new Date(),
      model: session.model,
      provider: session.provider,
      
      promptTokens: message.usage.promptTokens,
      completionTokens: message.usage.completionTokens,
      cachedTokens: message.usage.cachedTokens ?? 0,
      totalTokens: message.usage.promptTokens + message.usage.completionTokens,
      
      cost: this.calculateCost(message.usage, session.model),
      diemCost: this.calculateDiemCost(message.usage),
      
      latencyMs: message.latencyMs ?? 0,
      durationMs: message.durationMs ?? 0,
      tokensPerSecond: this.calculateTPS(message)
    };
    
    this.db.insertMessageMetrics(metrics);
    this.updateSessionMetrics(session.id, metrics);
  }
  
  private calculateCost(usage: Usage, model: string): number {
    const pricing = MODEL_PRICING[model];
    if (!pricing) return 0;
    
    return (
      (usage.promptTokens / 1000) * pricing.inputCostPer1K +
      (usage.completionTokens / 1000) * pricing.outputCostPer1K
    );
  }
  
  private calculateDiemCost(usage: Usage): number {
    // Diem is consumed at same rate as USD
    // But only tracked if balance was positive
    return this.calculateCost(usage, usage.model);
  }
}
```

### From Venice API Headers

```typescript
// Called after every Venice API response
recordBalanceSnapshot(headers: Headers): void {
  const diem = parseFloat(headers.get('x-venice-balance-diem') ?? '');
  const usd = parseFloat(headers.get('x-venice-balance-usd') ?? '');
  
  if (!isNaN(diem)) {
    this.db.insertBalanceSnapshot({
      timestamp: new Date(),
      diem,
      usd: isNaN(usd) ? null : usd
    });
  }
}
```

---

## Storage Schema

### SQLite Tables

```sql
-- Per-message metrics
CREATE TABLE message_metrics (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  message_id TEXT NOT NULL,
  session_id TEXT NOT NULL,
  timestamp TEXT NOT NULL,
  model TEXT NOT NULL,
  provider TEXT NOT NULL,
  
  prompt_tokens INTEGER NOT NULL,
  completion_tokens INTEGER NOT NULL,
  cached_tokens INTEGER DEFAULT 0,
  total_tokens INTEGER NOT NULL,
  
  cost_usd REAL NOT NULL,
  diem_cost REAL,
  
  latency_ms INTEGER,
  duration_ms INTEGER,
  tokens_per_second REAL,
  
  created_at TEXT DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX idx_message_metrics_session ON message_metrics(session_id);
CREATE INDEX idx_message_metrics_timestamp ON message_metrics(timestamp);
CREATE INDEX idx_message_metrics_model ON message_metrics(model);

-- Session aggregates (updated incrementally)
CREATE TABLE session_metrics (
  session_id TEXT PRIMARY KEY,
  started_at TEXT NOT NULL,
  last_activity_at TEXT NOT NULL,
  
  message_count INTEGER DEFAULT 0,
  total_prompt_tokens INTEGER DEFAULT 0,
  total_completion_tokens INTEGER DEFAULT 0,
  total_cost_usd REAL DEFAULT 0,
  
  models_used TEXT,  -- JSON array
  
  updated_at TEXT DEFAULT CURRENT_TIMESTAMP
);

-- Balance snapshots for Diem tracking
CREATE TABLE balance_snapshots (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  timestamp TEXT NOT NULL,
  diem REAL NOT NULL,
  usd REAL,
  
  created_at TEXT DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX idx_balance_snapshots_timestamp ON balance_snapshots(timestamp);

-- Pre-aggregated hourly stats
CREATE TABLE hourly_stats (
  hour TEXT PRIMARY KEY,  -- ISO date truncated to hour
  
  prompt_tokens INTEGER DEFAULT 0,
  completion_tokens INTEGER DEFAULT 0,
  total_cost_usd REAL DEFAULT 0,
  message_count INTEGER DEFAULT 0,
  session_count INTEGER DEFAULT 0,
  
  updated_at TEXT DEFAULT CURRENT_TIMESTAMP
);

-- Pre-aggregated daily stats
CREATE TABLE daily_stats (
  day TEXT PRIMARY KEY,  -- ISO date (YYYY-MM-DD)
  
  prompt_tokens INTEGER DEFAULT 0,
  completion_tokens INTEGER DEFAULT 0,
  total_cost_usd REAL DEFAULT 0,
  message_count INTEGER DEFAULT 0,
  session_count INTEGER DEFAULT 0,
  
  diem_used REAL DEFAULT 0,
  diem_reset_amount REAL,  -- Balance at start of day
  
  updated_at TEXT DEFAULT CURRENT_TIMESTAMP
);
```

---

## Aggregation

### Real-Time Aggregation

```typescript
// bridge/src/metrics/aggregator.ts

class MetricsAggregator {
  private db: Database;
  
  // Update hourly stats when new message recorded
  updateHourlyStats(metrics: MessageMetrics): void {
    const hour = truncateToHour(metrics.timestamp);
    
    this.db.run(`
      INSERT INTO hourly_stats (hour, prompt_tokens, completion_tokens, total_cost_usd, message_count)
      VALUES (?, ?, ?, ?, 1)
      ON CONFLICT(hour) DO UPDATE SET
        prompt_tokens = prompt_tokens + excluded.prompt_tokens,
        completion_tokens = completion_tokens + excluded.completion_tokens,
        total_cost_usd = total_cost_usd + excluded.total_cost_usd,
        message_count = message_count + 1,
        updated_at = CURRENT_TIMESTAMP
    `, [hour, metrics.promptTokens, metrics.completionTokens, metrics.cost]);
  }
  
  // Update daily stats
  updateDailyStats(metrics: MessageMetrics): void {
    const day = truncateToDay(metrics.timestamp);
    
    this.db.run(`
      INSERT INTO daily_stats (day, prompt_tokens, completion_tokens, total_cost_usd, message_count, diem_used)
      VALUES (?, ?, ?, ?, 1, ?)
      ON CONFLICT(day) DO UPDATE SET
        prompt_tokens = prompt_tokens + excluded.prompt_tokens,
        completion_tokens = completion_tokens + excluded.completion_tokens,
        total_cost_usd = total_cost_usd + excluded.total_cost_usd,
        message_count = message_count + 1,
        diem_used = diem_used + excluded.diem_used,
        updated_at = CURRENT_TIMESTAMP
    `, [day, metrics.promptTokens, metrics.completionTokens, metrics.cost, metrics.diemCost]);
  }
}
```

### Query Helpers

```typescript
// Get usage for time range
async getUsageForRange(start: Date, end: Date): Promise<TimeSeriesPoint[]> {
  // Determine appropriate bucket size
  const rangeHours = (end.getTime() - start.getTime()) / (1000 * 60 * 60);
  
  if (rangeHours <= 24) {
    // Use hourly buckets
    return this.db.all(`
      SELECT 
        hour as timestamp,
        'hour' as bucketSize,
        prompt_tokens as promptTokens,
        completion_tokens as completionTokens,
        total_cost_usd as totalCost,
        message_count as messageCount,
        session_count as sessionCount
      FROM hourly_stats
      WHERE hour >= ? AND hour < ?
      ORDER BY hour
    `, [start.toISOString(), end.toISOString()]);
  } else {
    // Use daily buckets
    return this.db.all(`
      SELECT 
        day as timestamp,
        'day' as bucketSize,
        prompt_tokens as promptTokens,
        completion_tokens as completionTokens,
        total_cost_usd as totalCost,
        message_count as messageCount,
        session_count as sessionCount
      FROM daily_stats
      WHERE day >= ? AND day < ?
      ORDER BY day
    `, [formatDate(start), formatDate(end)]);
  }
}

// Get today's usage
async getTodayUsage(): Promise<DailyUsage> {
  const today = formatDate(new Date());
  
  const row = await this.db.get(`
    SELECT * FROM daily_stats WHERE day = ?
  `, [today]);
  
  return row ?? {
    promptTokens: 0,
    completionTokens: 0,
    totalCost: 0,
    messageCount: 0,
    diemUsed: 0
  };
}

// Get usage by model
async getUsageByModel(start: Date, end: Date): Promise<ModelUsage[]> {
  return this.db.all(`
    SELECT 
      model,
      SUM(prompt_tokens) as promptTokens,
      SUM(completion_tokens) as completionTokens,
      SUM(cost_usd) as cost,
      COUNT(*) as messageCount
    FROM message_metrics
    WHERE timestamp >= ? AND timestamp < ?
    GROUP BY model
    ORDER BY cost DESC
  `, [start.toISOString(), end.toISOString()]);
}
```

---

## Consumption Rate Calculation

### Algorithm

```typescript
// Calculate tokens/hour consumption rate
calculateConsumptionRate(snapshots: BalanceSnapshot[]): number {
  // Need at least 2 snapshots
  if (snapshots.length < 2) return 0;
  
  // Use snapshots from last hour
  const oneHourAgo = new Date(Date.now() - 60 * 60 * 1000);
  const recent = snapshots.filter(s => s.timestamp >= oneHourAgo);
  
  if (recent.length < 2) {
    // Fall back to all available snapshots
    const first = snapshots[0];
    const last = snapshots[snapshots.length - 1];
    const hoursDiff = (last.timestamp - first.timestamp) / (1000 * 60 * 60);
    
    if (hoursDiff < 0.1) return 0;  // Not enough time elapsed
    
    return (first.diem - last.diem) / hoursDiff;
  }
  
  // Weighted average of recent consumption
  let totalConsumption = 0;
  let totalWeight = 0;
  
  for (let i = 1; i < recent.length; i++) {
    const prev = recent[i - 1];
    const curr = recent[i];
    
    const consumption = prev.diem - curr.diem;
    const hours = (curr.timestamp - prev.timestamp) / (1000 * 60 * 60);
    
    if (hours > 0 && consumption >= 0) {
      // More recent = higher weight
      const weight = i / recent.length;
      totalConsumption += (consumption / hours) * weight;
      totalWeight += weight;
    }
  }
  
  return totalWeight > 0 ? totalConsumption / totalWeight : 0;
}

// Estimate time until depletion
calculateTimeToDepletion(currentDiem: number, rate: number): number | null {
  if (rate <= 0) return null;  // Not consuming or gaining
  
  const hoursRemaining = currentDiem / rate;
  return hoursRemaining;
}
```

---

## Data Retention

### Automatic Cleanup

```typescript
// Run daily to manage storage
async cleanupOldData(): Promise<void> {
  const retentionDays = this.config.storage.sessionRetentionDays;
  const cutoff = new Date();
  cutoff.setDate(cutoff.getDate() - retentionDays);
  
  // Delete old message metrics (keep aggregates)
  await this.db.run(`
    DELETE FROM message_metrics 
    WHERE timestamp < ?
  `, [cutoff.toISOString()]);
  
  // Keep hourly stats for 7 days
  const hourlyCutoff = new Date();
  hourlyCutoff.setDate(hourlyCutoff.getDate() - 7);
  await this.db.run(`
    DELETE FROM hourly_stats 
    WHERE hour < ?
  `, [hourlyCutoff.toISOString()]);
  
  // Keep daily stats indefinitely (small)
  // Keep balance snapshots for 30 days
  const balanceCutoff = new Date();
  balanceCutoff.setDate(balanceCutoff.getDate() - 30);
  await this.db.run(`
    DELETE FROM balance_snapshots 
    WHERE timestamp < ?
  `, [balanceCutoff.toISOString()]);
  
  // Vacuum to reclaim space
  await this.db.run('VACUUM');
}
```

---

## Broadcasting to Browser

```typescript
// When metrics update, broadcast to connected browsers
metricsCollector.on('messageRecorded', (metrics) => {
  wsManager.broadcast({
    jsonrpc: '2.0',
    method: 'usage.update',
    params: {
      type: 'message',
      sessionId: metrics.sessionId,
      promptTokens: metrics.promptTokens,
      completionTokens: metrics.completionTokens,
      cost: metrics.cost,
      timestamp: metrics.timestamp
    }
  });
});
```

---

## Related Specifications

- `11-DIEM-TRACKING.md` - Balance tracking
- `53-TOKEN-USAGE-CHART.md` - Visualization
- `15-COST-PROJECTION.md` - Forecasting

---

*"What gets measured gets managed."*
