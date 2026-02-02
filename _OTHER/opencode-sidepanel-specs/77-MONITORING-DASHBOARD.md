# 77-MONITORING-DASHBOARD: Observability and Metrics

## Overview

The monitoring dashboard provides real-time visibility into system health, performance, and usage patterns.

---

## Dashboard Views

### 1. System Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  SYSTEM OVERVIEW                                         Last 24 hours     │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ HEALTH ────────┐  ┌─ UPTIME ───────┐  ┌─ ERRORS ───────┐              │
│  │                 │  │                 │  │                 │              │
│  │   ● HEALTHY     │  │   99.95%        │  │   3             │              │
│  │                 │  │   (23h 59m)     │  │   last 24h      │              │
│  └─────────────────┘  └─────────────────┘  └─────────────────┘              │
│                                                                             │
│  ┌─ CONNECTIONS ───────────────────────────────────────────────────────┐   │
│  │   ▁▂▃▄▅▆▇█▇▆▅▄▃▂▁▂▃▄▅▆▇▆▅▄▃▂▁▂▃▄▅▆▇█▇▆▅▄▃▂▁                        │   │
│  │   Current: 8        Peak: 23        Avg: 12                         │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  ┌─ REQUESTS/MIN ──────────────────────────────────────────────────────┐   │
│  │   ▂▃▄▆▇█▇▆▅▅▆▇█▇▆▅▄▃▂▂▃▄▅▆▇▇▆▅▄▃▂▂▃▄▅▆▇█▇▆▅                        │   │
│  │   Current: 145      Peak: 320       Avg: 180                        │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 2. Venice API Metrics

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  VENICE API                                              Last 24 hours     │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ BALANCE ──────────────────────────────────────────────────────────┐    │
│  │                                                                     │    │
│  │  100 ┤                                                              │    │
│  │   80 ┤████▀▀▀▀▀▀▀                                                  │    │
│  │   60 ┤           ▀▀▀▀▀▀▀▀▀                                         │    │
│  │   40 ┤                    ▀▀▀▀▀▀▀▀                                  │    │
│  │   20 ┤                           ▀▀▀▀▀█████████████████████        │    │
│  │    0 ┼────────────────────────────────────────────────────────     │    │
│  │      00:00           06:00           12:00           18:00         │    │
│  │                                                                     │    │
│  │  Current: 42.5 Diem    Reset in: 4h 23m    Burn rate: 5.2/hr       │    │
│  │                                                                     │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                                                             │
│  ┌─ API LATENCY ─────────┐  ┌─ TOKENS TODAY ─────┐  ┌─ COST ──────────┐   │
│  │                       │  │                     │  │                  │   │
│  │  p50: 120ms          │  │  Prompt: 45,231    │  │  Today: $0.045   │   │
│  │  p95: 350ms          │  │  Completion: 23,456 │  │  Week: $0.312    │   │
│  │  p99: 890ms          │  │  Total: 68,687     │  │  Month: $1.24    │   │
│  │                       │  │                     │  │                  │   │
│  └───────────────────────┘  └─────────────────────┘  └──────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 3. Session Analytics

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  SESSION ANALYTICS                                       Last 7 days       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ SESSIONS CREATED ─────────────────────────────────────────────────┐    │
│  │                                                                     │    │
│  │   Mon    Tue    Wed    Thu    Fri    Sat    Sun                    │    │
│  │    ▇      ▅      ▇      █      ▆      ▂      ▃                     │    │
│  │   12      8     14     18     11      3      5        Total: 71    │    │
│  │                                                                     │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                                                             │
│  ┌─ TOP MODELS ──────────┐  ┌─ AVG SESSION ─────┐  ┌─ ACTIVE NOW ────┐    │
│  │                       │  │                    │  │                  │    │
│  │  llama-3.3-70b  65%  │  │  Duration: 23min  │  │       3          │    │
│  │  qwen-2.5-72b   20%  │  │  Messages: 12     │  │   sessions       │    │
│  │  deepseek-r1    15%  │  │  Tokens: 8,500    │  │                  │    │
│  │                       │  │                    │  │                  │    │
│  └───────────────────────┘  └────────────────────┘  └──────────────────┘    │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Metrics Schema

```typescript
interface SystemMetrics {
  timestamp: Date;
  
  // Health
  status: 'healthy' | 'degraded' | 'unhealthy';
  uptime: number;
  
  // Connections
  activeConnections: number;
  peakConnections: number;
  totalConnections: number;
  
  // Requests
  requestsPerMinute: number;
  requestsTotal: number;
  errorRate: number;
  
  // Latency
  latencyP50: number;
  latencyP95: number;
  latencyP99: number;
  
  // Resources
  cpuUsage: number;
  memoryUsage: number;
  diskUsage: number;
}

interface VeniceMetrics {
  timestamp: Date;
  
  // Balance
  balanceDiem: number;
  balanceUsd: number;
  burnRate: number;
  timeToReset: number;
  
  // Usage
  promptTokens: number;
  completionTokens: number;
  totalTokens: number;
  totalCost: number;
  
  // API
  requestsTotal: number;
  errorsTotal: number;
  latencyP50: number;
  latencyP95: number;
  
  // Rate limits
  rateLimitRemaining: number;
  rateLimitTotal: number;
}

interface SessionMetrics {
  timestamp: Date;
  
  // Counts
  activeSessions: number;
  totalSessions: number;
  sessionsCreatedToday: number;
  
  // Averages
  avgDuration: number;
  avgMessages: number;
  avgTokens: number;
  
  // Models
  modelUsage: Record<string, number>;
}
```

---

## Prometheus Metrics

```typescript
// bridge/src/metrics/prometheus.ts

import { Counter, Gauge, Histogram, Registry } from 'prom-client';

export const registry = new Registry();

// Connection metrics
export const activeConnections = new Gauge({
  name: 'sidepanel_ws_active_connections',
  help: 'Number of active WebSocket connections',
  registers: [registry]
});

export const connectionTotal = new Counter({
  name: 'sidepanel_ws_connections_total',
  help: 'Total WebSocket connections',
  registers: [registry]
});

// Request metrics
export const requestDuration = new Histogram({
  name: 'sidepanel_request_duration_seconds',
  help: 'Request duration in seconds',
  buckets: [0.01, 0.05, 0.1, 0.25, 0.5, 1, 2.5, 5],
  labelNames: ['method'],
  registers: [registry]
});

export const requestTotal = new Counter({
  name: 'sidepanel_requests_total',
  help: 'Total requests',
  labelNames: ['method', 'status'],
  registers: [registry]
});

// Venice metrics
export const veniceBalance = new Gauge({
  name: 'sidepanel_venice_balance_diem',
  help: 'Current Venice Diem balance',
  registers: [registry]
});

export const veniceTokens = new Counter({
  name: 'sidepanel_venice_tokens_total',
  help: 'Total tokens used',
  labelNames: ['type'],
  registers: [registry]
});

// Session metrics
export const activeSessions = new Gauge({
  name: 'sidepanel_sessions_active',
  help: 'Number of active sessions',
  registers: [registry]
});

// Expose /metrics endpoint
export function metricsHandler(req: Request, res: Response) {
  res.set('Content-Type', registry.contentType);
  res.end(registry.metrics());
}
```

---

## Grafana Configuration

```yaml
# grafana/dashboards/sidepanel.yml
apiVersion: 1
providers:
  - name: 'Sidepanel'
    folder: 'Sidepanel'
    type: file
    options:
      path: /var/lib/grafana/dashboards/sidepanel
```

```json
{
  "dashboard": {
    "title": "Sidepanel Overview",
    "panels": [
      {
        "title": "Active Connections",
        "type": "stat",
        "targets": [{
          "expr": "sidepanel_ws_active_connections"
        }]
      },
      {
        "title": "Request Rate",
        "type": "graph",
        "targets": [{
          "expr": "rate(sidepanel_requests_total[5m])"
        }]
      },
      {
        "title": "Latency Distribution",
        "type": "heatmap",
        "targets": [{
          "expr": "rate(sidepanel_request_duration_seconds_bucket[5m])"
        }]
      },
      {
        "title": "Venice Balance",
        "type": "gauge",
        "targets": [{
          "expr": "sidepanel_venice_balance_diem"
        }],
        "options": {
          "min": 0,
          "max": 100,
          "thresholds": [
            { "value": 10, "color": "red" },
            { "value": 25, "color": "yellow" },
            { "value": 50, "color": "green" }
          ]
        }
      }
    ]
  }
}
```

---

## Alerting Rules

```yaml
# prometheus/alerts.yml
groups:
  - name: sidepanel
    rules:
      - alert: HighErrorRate
        expr: rate(sidepanel_requests_total{status="error"}[5m]) > 0.05
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High error rate detected"
          
      - alert: LowDiemBalance
        expr: sidepanel_venice_balance_diem < 10
        for: 1m
        labels:
          severity: warning
        annotations:
          summary: "Venice balance below 10 Diem"
          
      - alert: CriticalDiemBalance
        expr: sidepanel_venice_balance_diem < 5
        for: 1m
        labels:
          severity: critical
        annotations:
          summary: "Venice balance critically low"
          
      - alert: HighLatency
        expr: histogram_quantile(0.95, rate(sidepanel_request_duration_seconds_bucket[5m])) > 1
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "P95 latency above 1 second"
```

---

## Related Specifications

- `38-LOGGING-MONITORING.md` - Logging system
- `39-HEALTH-CHECKS.md` - Health endpoints
- `67-PERFORMANCE-PROFILER.md` - Performance analysis

---

*"You can't improve what you can't measure."*
