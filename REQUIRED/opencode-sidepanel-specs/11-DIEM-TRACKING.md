# 11-DIEM-TRACKING: Balance Tracking Implementation

## Overview

Diem tracking is the foundation of cost visibility in the sidepanel. Every Venice API response includes balance headers, and our job is to:

1. Extract balance from every response
2. Aggregate usage metrics over time
3. Calculate consumption rate
4. Project balance depletion
5. Display status in real-time

---

## Data Model

### Balance State

```typescript
interface DiemState {
  // Current balances
  diem: number;                     // From x-venice-balance-diem
  usd: number;                      // From x-venice-balance-usd
  
  // Effective balance (diem + usd)
  effective: number;
  
  // Last update metadata
  lastUpdated: Date;
  lastSource: 'api' | 'websocket' | 'manual';
  
  // Historical data for rate calculation
  history: BalanceSnapshot[];
  
  // Computed metrics
  metrics: DiemMetrics;
}

interface BalanceSnapshot {
  timestamp: Date;
  diem: number;
  usd: number;
  trigger: 'api_response' | 'periodic' | 'reset';
}

interface DiemMetrics {
  // Consumption rate
  consumptionRate: number;          // Diem per hour
  costRate: number;                 // USD equivalent per hour
  
  // Projections
  timeToDepletion: Duration | null; // null if rate is 0
  projectedBalance: number;         // At end of day
  
  // Period stats
  todayUsed: number;                // Diem consumed today
  todayRemaining: number;           // Until midnight UTC
  
  // Trends
  averageDaily: number;             // Rolling 7-day average
  peakHourly: number;               // Highest hourly rate today
}
```

### PureScript Type Definitions

```purescript
module Sidepanel.State.Diem where

import Prelude
import Data.DateTime (DateTime)
import Data.Time.Duration (Hours, Minutes)
import Data.Maybe (Maybe)
import Data.Array (Array)

type DiemState =
  { diem :: Number
  , usd :: Number
  , effective :: Number
  , lastUpdated :: DateTime
  , history :: Array BalanceSnapshot
  , metrics :: DiemMetrics
  }

type BalanceSnapshot =
  { timestamp :: DateTime
  , diem :: Number
  , usd :: Number
  }

type DiemMetrics =
  { consumptionRate :: Number      -- per hour
  , timeToDepletion :: Maybe Hours
  , todayUsed :: Number
  , todayRemaining :: Number
  }

initialDiemState :: DiemState
initialDiemState =
  { diem: 0.0
  , usd: 0.0
  , effective: 0.0
  , lastUpdated: bottom
  , history: []
  , metrics: initialMetrics
  }
```

---

## Balance Extraction

### From API Response Headers

```typescript
// Called after EVERY Venice API response
function extractBalance(response: Response): Balance {
  const headers = response.headers;
  
  const diem = parseFloat(headers.get('x-venice-balance-diem') ?? '0');
  const usd = parseFloat(headers.get('x-venice-balance-usd') ?? '0');
  
  // Validate: balances should never be negative
  if (diem < 0 || usd < 0) {
    console.warn('Invalid balance received:', { diem, usd });
    // Don't update state with invalid data
    return getCurrentBalance();
  }
  
  return { diem, usd, effective: diem + usd };
}

// Update state with new balance
function updateBalance(balance: Balance): void {
  const now = new Date();
  const snapshot: BalanceSnapshot = {
    timestamp: now,
    diem: balance.diem,
    usd: balance.usd,
    trigger: 'api_response'
  };
  
  // Add to history (keep last 24 hours)
  state.history = [
    ...state.history.filter(s => 
      now.getTime() - s.timestamp.getTime() < 24 * 60 * 60 * 1000
    ),
    snapshot
  ];
  
  // Update current values
  state.diem = balance.diem;
  state.usd = balance.usd;
  state.effective = balance.effective;
  state.lastUpdated = now;
  state.lastSource = 'api';
  
  // Recalculate metrics
  state.metrics = calculateMetrics(state.history);
  
  // Emit update event
  emitBalanceUpdate(state);
}
```

### Handling Missing Headers

```typescript
// Some responses might not include balance headers
// (e.g., errors, certain endpoints)

function safeExtractBalance(response: Response): Balance | null {
  const diemHeader = response.headers.get('x-venice-balance-diem');
  const usdHeader = response.headers.get('x-venice-balance-usd');
  
  // If headers are missing, return null (don't update state)
  if (diemHeader === null && usdHeader === null) {
    return null;
  }
  
  // If one is present, the other should be too (warn if not)
  if (diemHeader === null || usdHeader === null) {
    console.warn('Partial balance headers received');
  }
  
  return extractBalance(response);
}
```

---

## Consumption Rate Calculation

### Algorithm

```typescript
function calculateConsumptionRate(history: BalanceSnapshot[]): number {
  // Need at least 2 data points
  if (history.length < 2) return 0;
  
  // Get snapshots from last hour
  const now = Date.now();
  const oneHourAgo = now - 60 * 60 * 1000;
  const recentSnapshots = history.filter(s => 
    s.timestamp.getTime() > oneHourAgo
  );
  
  if (recentSnapshots.length < 2) {
    // Fall back to longer window if not enough recent data
    return calculateLongTermRate(history);
  }
  
  // Calculate rate from most recent decline
  const sorted = [...recentSnapshots].sort(
    (a, b) => a.timestamp.getTime() - b.timestamp.getTime()
  );
  
  const first = sorted[0];
  const last = sorted[sorted.length - 1];
  
  // Only Diem depletes (USD is deposited)
  const diemDelta = first.diem - last.diem;
  const timeDeltaHours = (last.timestamp.getTime() - first.timestamp.getTime()) / (60 * 60 * 1000);
  
  if (timeDeltaHours === 0) return 0;
  
  // Rate in Diem per hour (positive = consuming)
  const rate = Math.max(0, diemDelta / timeDeltaHours);
  
  return rate;
}

function calculateLongTermRate(history: BalanceSnapshot[]): number {
  // Use full history with weighted average (recent = more weight)
  if (history.length < 2) return 0;
  
  const sorted = [...history].sort(
    (a, b) => a.timestamp.getTime() - b.timestamp.getTime()
  );
  
  let totalWeightedRate = 0;
  let totalWeight = 0;
  
  for (let i = 1; i < sorted.length; i++) {
    const prev = sorted[i - 1];
    const curr = sorted[i];
    
    const diemDelta = prev.diem - curr.diem;
    const timeDeltaHours = (curr.timestamp.getTime() - prev.timestamp.getTime()) / (60 * 60 * 1000);
    
    if (timeDeltaHours > 0 && diemDelta > 0) {
      const rate = diemDelta / timeDeltaHours;
      const recency = i / sorted.length;  // 0 to 1, higher = more recent
      const weight = Math.pow(recency, 2);  // Square for stronger recency bias
      
      totalWeightedRate += rate * weight;
      totalWeight += weight;
    }
  }
  
  return totalWeight > 0 ? totalWeightedRate / totalWeight : 0;
}
```

### Time to Depletion

```typescript
function calculateTimeToDepletion(
  currentDiem: number,
  rate: number  // Diem per hour
): Duration | null {
  if (rate <= 0) return null;  // Not depleting
  if (currentDiem <= 0) return Duration.zero;  // Already depleted
  
  const hours = currentDiem / rate;
  return Duration.fromHours(hours);
}

// For display: "4h 23m" or "2d 5h" or "< 1h"
function formatTimeToDepletion(duration: Duration | null): string {
  if (duration === null) return '∞';  // Not depleting
  
  const totalMinutes = duration.toMinutes();
  
  if (totalMinutes < 60) {
    return `${Math.ceil(totalMinutes)}m`;
  }
  
  const hours = Math.floor(totalMinutes / 60);
  const minutes = Math.round(totalMinutes % 60);
  
  if (hours < 24) {
    return minutes > 0 ? `${hours}h ${minutes}m` : `${hours}h`;
  }
  
  const days = Math.floor(hours / 24);
  const remainingHours = hours % 24;
  return `${days}d ${remainingHours}h`;
}
```

---

## Today's Usage Tracking

### Detecting Day Boundary

```typescript
// Diem resets at midnight UTC
function getStartOfDiemDay(): Date {
  const now = new Date();
  const utcMidnight = new Date(Date.UTC(
    now.getUTCFullYear(),
    now.getUTCMonth(),
    now.getUTCDate(),
    0, 0, 0, 0
  ));
  return utcMidnight;
}

function getTodayUsage(history: BalanceSnapshot[]): number {
  const dayStart = getStartOfDiemDay();
  const todaySnapshots = history.filter(s => 
    s.timestamp >= dayStart
  );
  
  if (todaySnapshots.length === 0) return 0;
  
  // First snapshot of the day (or first after reset)
  const sorted = [...todaySnapshots].sort(
    (a, b) => a.timestamp.getTime() - b.timestamp.getTime()
  );
  
  const firstOfDay = sorted[0];
  const latest = sorted[sorted.length - 1];
  
  // Usage = first balance - current balance (for Diem only)
  return Math.max(0, firstOfDay.diem - latest.diem);
}
```

### Handling Reset Detection

```typescript
// Detect when Diem balance jumps up (reset occurred)
function detectReset(
  previousBalance: number,
  currentBalance: number,
  currentTime: Date
): boolean {
  // Balance increased significantly
  const significantIncrease = currentBalance > previousBalance * 1.5;
  
  // And it's within 5 minutes of midnight UTC
  const utcHours = currentTime.getUTCHours();
  const utcMinutes = currentTime.getUTCMinutes();
  const nearMidnight = utcHours === 0 && utcMinutes < 5;
  
  return significantIncrease && nearMidnight;
}

// When reset detected
function handleDiemReset(): void {
  // Clear today's history (new day)
  const dayStart = getStartOfDiemDay();
  state.history = state.history.filter(s => s.timestamp >= dayStart);
  
  // Record reset snapshot
  state.history.push({
    timestamp: new Date(),
    diem: state.diem,
    usd: state.usd,
    trigger: 'reset'
  });
  
  // Reset today's metrics
  state.metrics.todayUsed = 0;
  
  // Emit reset event for UI
  emitResetEvent();
}
```

---

## Metrics Aggregation

### Full Metrics Calculation

```typescript
function calculateMetrics(history: BalanceSnapshot[]): DiemMetrics {
  const consumptionRate = calculateConsumptionRate(history);
  const todayUsed = getTodayUsage(history);
  const todayRemaining = calculateTimeToDepletion(state.diem, consumptionRate);
  
  // Average daily (last 7 days)
  const averageDaily = calculateAverageDaily(history);
  
  // Peak hourly rate today
  const peakHourly = calculatePeakHourlyRate(history);
  
  // Cost rate (USD per hour)
  // Diem = $1 equivalent
  const costRate = consumptionRate;  // 1 Diem = $1
  
  // Projected balance at end of day
  const hoursUntilReset = getHoursUntilReset();
  const projectedUsage = consumptionRate * hoursUntilReset;
  const projectedBalance = Math.max(0, state.diem - projectedUsage);
  
  return {
    consumptionRate,
    costRate,
    timeToDepletion: todayRemaining,
    projectedBalance,
    todayUsed,
    todayRemaining: state.diem,
    averageDaily,
    peakHourly
  };
}

function calculateAverageDaily(history: BalanceSnapshot[]): number {
  // Get data from last 7 days
  const sevenDaysAgo = Date.now() - 7 * 24 * 60 * 60 * 1000;
  const weekHistory = history.filter(s => 
    s.timestamp.getTime() > sevenDaysAgo
  );
  
  if (weekHistory.length < 2) return 0;
  
  // Group by day
  const byDay = new Map<string, BalanceSnapshot[]>();
  for (const snapshot of weekHistory) {
    const dayKey = snapshot.timestamp.toISOString().split('T')[0];
    if (!byDay.has(dayKey)) byDay.set(dayKey, []);
    byDay.get(dayKey)!.push(snapshot);
  }
  
  // Calculate daily usage for each day
  const dailyUsages: number[] = [];
  for (const [_, daySnapshots] of byDay) {
    if (daySnapshots.length < 2) continue;
    const sorted = [...daySnapshots].sort(
      (a, b) => a.timestamp.getTime() - b.timestamp.getTime()
    );
    const usage = Math.max(0, sorted[0].diem - sorted[sorted.length - 1].diem);
    dailyUsages.push(usage);
  }
  
  if (dailyUsages.length === 0) return 0;
  return dailyUsages.reduce((a, b) => a + b, 0) / dailyUsages.length;
}
```

---

## State Persistence

### Storage Schema

```typescript
// SQLite schema for session storage
const SCHEMA = `
  CREATE TABLE IF NOT EXISTS diem_snapshots (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    timestamp INTEGER NOT NULL,
    diem REAL NOT NULL,
    usd REAL NOT NULL,
    trigger TEXT NOT NULL,
    session_id TEXT
  );
  
  CREATE INDEX IF NOT EXISTS idx_snapshots_timestamp 
    ON diem_snapshots(timestamp);
`;

// Prune old data (keep 30 days)
const PRUNE_QUERY = `
  DELETE FROM diem_snapshots 
  WHERE timestamp < ?
`;
```

### Save and Load

```typescript
async function saveSnapshot(snapshot: BalanceSnapshot): Promise<void> {
  await db.run(
    `INSERT INTO diem_snapshots (timestamp, diem, usd, trigger, session_id)
     VALUES (?, ?, ?, ?, ?)`,
    [
      snapshot.timestamp.getTime(),
      snapshot.diem,
      snapshot.usd,
      snapshot.trigger,
      currentSessionId
    ]
  );
}

async function loadHistory(since: Date): Promise<BalanceSnapshot[]> {
  const rows = await db.all(
    `SELECT timestamp, diem, usd, trigger 
     FROM diem_snapshots 
     WHERE timestamp > ?
     ORDER BY timestamp ASC`,
    [since.getTime()]
  );
  
  return rows.map(row => ({
    timestamp: new Date(row.timestamp),
    diem: row.diem,
    usd: row.usd,
    trigger: row.trigger as BalanceSnapshot['trigger']
  }));
}
```

---

## WebSocket Broadcasting

### Balance Update Message

```typescript
interface BalanceUpdateMessage {
  jsonrpc: '2.0';
  method: 'balance.update';
  params: {
    diem: number;
    usd: number;
    effective: number;
    metrics: DiemMetrics;
    timestamp: string;  // ISO 8601
  };
}

function broadcastBalanceUpdate(state: DiemState): void {
  const message: BalanceUpdateMessage = {
    jsonrpc: '2.0',
    method: 'balance.update',
    params: {
      diem: state.diem,
      usd: state.usd,
      effective: state.effective,
      metrics: state.metrics,
      timestamp: state.lastUpdated.toISOString()
    }
  };
  
  wss.clients.forEach(client => {
    if (client.readyState === WebSocket.OPEN) {
      client.send(JSON.stringify(message));
    }
  });
}
```

---

## Alert Thresholds

### Configuration

```typescript
interface AlertConfig {
  // Percentage thresholds
  warningPercent: number;   // Default: 20%
  criticalPercent: number;  // Default: 5%
  
  // Absolute thresholds
  warningAbsolute: number;  // Default: 5 Diem
  criticalAbsolute: number; // Default: 1 Diem
  
  // Time-based
  depletionWarningHours: number;  // Warn if depleting within N hours
}

const DEFAULT_ALERTS: AlertConfig = {
  warningPercent: 0.20,
  criticalPercent: 0.05,
  warningAbsolute: 5,
  criticalAbsolute: 1,
  depletionWarningHours: 2
};
```

### Alert Logic

```typescript
type AlertLevel = 'none' | 'warning' | 'critical';

function getAlertLevel(state: DiemState, config: AlertConfig): AlertLevel {
  const { diem, metrics } = state;
  
  // Critical checks (highest priority)
  if (diem <= config.criticalAbsolute) return 'critical';
  if (diem <= state.initialDiem * config.criticalPercent) return 'critical';
  
  // Warning checks
  if (diem <= config.warningAbsolute) return 'warning';
  if (diem <= state.initialDiem * config.warningPercent) return 'warning';
  
  // Time-based warning
  if (metrics.timeToDepletion !== null) {
    const hoursRemaining = metrics.timeToDepletion.toHours();
    if (hoursRemaining < config.depletionWarningHours) return 'warning';
  }
  
  return 'none';
}
```

---

## Testing

### Unit Tests

```typescript
describe('Diem Tracking', () => {
  describe('Balance Extraction', () => {
    it('extracts balance from headers', () => {
      const response = new Response('{}', {
        headers: {
          'x-venice-balance-diem': '42.5',
          'x-venice-balance-usd': '10.00'
        }
      });
      
      const balance = extractBalance(response);
      
      expect(balance.diem).toBe(42.5);
      expect(balance.usd).toBe(10);
      expect(balance.effective).toBe(52.5);
    });
    
    it('handles missing headers', () => {
      const response = new Response('{}');
      
      const balance = safeExtractBalance(response);
      
      expect(balance).toBeNull();
    });
  });
  
  describe('Consumption Rate', () => {
    it('calculates rate from history', () => {
      const now = Date.now();
      const history: BalanceSnapshot[] = [
        { timestamp: new Date(now - 60 * 60 * 1000), diem: 10, usd: 0, trigger: 'api_response' },
        { timestamp: new Date(now), diem: 8, usd: 0, trigger: 'api_response' }
      ];
      
      const rate = calculateConsumptionRate(history);
      
      expect(rate).toBe(2);  // 2 Diem per hour
    });
  });
  
  describe('Time to Depletion', () => {
    it('calculates correctly', () => {
      const duration = calculateTimeToDepletion(10, 2);  // 10 Diem, 2/hour
      
      expect(duration?.toHours()).toBe(5);
    });
    
    it('returns null when not depleting', () => {
      const duration = calculateTimeToDepletion(10, 0);
      
      expect(duration).toBeNull();
    });
  });
});
```

---

## Related Specifications

- `10-VENICE-API-OVERVIEW.md` - API structure and headers
- `12-DIEM-RESET-COUNTDOWN.md` - Countdown timer implementation
- `15-COST-PROJECTION.md` - Advanced forecasting
- `51-DIEM-TRACKER-WIDGET.md` - UI component specification

---

*"Balance tracking is not a feature; it's the heartbeat of cost awareness."*
