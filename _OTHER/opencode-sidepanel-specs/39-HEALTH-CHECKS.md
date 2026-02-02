# 39-HEALTH-CHECKS: System Health Monitoring

## Overview

Health checks provide visibility into system status, enabling monitoring, alerting, and debugging of the sidepanel components.

---

## Health Check Endpoints

### Bridge Server Health

```
GET /health
GET /health/live
GET /health/ready
GET /health/detailed
```

---

## Response Format

### Simple Health Check

```http
GET /health HTTP/1.1

HTTP/1.1 200 OK
Content-Type: application/json

{
  "status": "healthy",
  "timestamp": "2025-01-15T14:32:05.123Z"
}
```

### Detailed Health Check

```http
GET /health/detailed HTTP/1.1

HTTP/1.1 200 OK
Content-Type: application/json

{
  "status": "healthy",
  "timestamp": "2025-01-15T14:32:05.123Z",
  "version": "0.1.0",
  "uptime": 3600000,
  "checks": {
    "database": {
      "status": "healthy",
      "latency": 5,
      "details": {
        "connections": 2,
        "maxConnections": 10
      }
    },
    "websocket": {
      "status": "healthy",
      "details": {
        "activeConnections": 3,
        "messagesPerMinute": 45
      }
    },
    "venice_api": {
      "status": "healthy",
      "latency": 120,
      "details": {
        "balanceDiem": 42.5,
        "rateLimit": {
          "remaining": 95,
          "limit": 100
        }
      }
    },
    "memory": {
      "status": "healthy",
      "details": {
        "heapUsed": 52428800,
        "heapTotal": 104857600,
        "external": 1048576,
        "percentUsed": 50
      }
    },
    "disk": {
      "status": "healthy",
      "details": {
        "used": 1073741824,
        "total": 10737418240,
        "percentUsed": 10
      }
    }
  }
}
```

### Unhealthy Response

```http
GET /health HTTP/1.1

HTTP/1.1 503 Service Unavailable
Content-Type: application/json

{
  "status": "unhealthy",
  "timestamp": "2025-01-15T14:32:05.123Z",
  "checks": {
    "database": {
      "status": "unhealthy",
      "error": "Connection timeout after 5000ms"
    },
    "venice_api": {
      "status": "degraded",
      "details": {
        "balanceDiem": 0.5,
        "warning": "Balance critically low"
      }
    }
  }
}
```

---

## Data Model

```typescript
interface HealthStatus {
  status: 'healthy' | 'degraded' | 'unhealthy';
  timestamp: Date;
  version: string;
  uptime: number;  // ms
  checks: Record<string, CheckResult>;
}

interface CheckResult {
  status: 'healthy' | 'degraded' | 'unhealthy';
  latency?: number;  // ms
  error?: string;
  details?: Record<string, unknown>;
}

type CheckName = 
  | 'database'
  | 'websocket'
  | 'venice_api'
  | 'memory'
  | 'disk'
  | 'plugin';
```

---

## Health Check Implementation

```typescript
// bridge/src/health/service.ts

export class HealthService {
  private checks: Map<string, HealthCheck> = new Map();
  private startTime: Date = new Date();
  
  constructor() {
    this.registerBuiltinChecks();
  }
  
  private registerBuiltinChecks(): void {
    this.register('database', new DatabaseCheck());
    this.register('websocket', new WebSocketCheck());
    this.register('venice_api', new VeniceApiCheck());
    this.register('memory', new MemoryCheck());
    this.register('disk', new DiskCheck());
  }
  
  register(name: string, check: HealthCheck): void {
    this.checks.set(name, check);
  }
  
  async getHealth(detailed: boolean = false): Promise<HealthStatus> {
    const results = await this.runAllChecks();
    const overallStatus = this.calculateOverallStatus(results);
    
    const status: HealthStatus = {
      status: overallStatus,
      timestamp: new Date(),
      version: process.env.VERSION ?? '0.1.0',
      uptime: Date.now() - this.startTime.getTime(),
      checks: detailed ? results : {}
    };
    
    return status;
  }
  
  private async runAllChecks(): Promise<Record<string, CheckResult>> {
    const results: Record<string, CheckResult> = {};
    
    await Promise.all(
      Array.from(this.checks.entries()).map(async ([name, check]) => {
        try {
          const start = Date.now();
          const result = await Promise.race([
            check.run(),
            this.timeout(check.timeout)
          ]);
          result.latency = Date.now() - start;
          results[name] = result;
        } catch (error) {
          results[name] = {
            status: 'unhealthy',
            error: error.message
          };
        }
      })
    );
    
    return results;
  }
  
  private calculateOverallStatus(
    results: Record<string, CheckResult>
  ): 'healthy' | 'degraded' | 'unhealthy' {
    const statuses = Object.values(results).map(r => r.status);
    
    if (statuses.includes('unhealthy')) {
      return 'unhealthy';
    }
    
    if (statuses.includes('degraded')) {
      return 'degraded';
    }
    
    return 'healthy';
  }
  
  private timeout(ms: number): Promise<never> {
    return new Promise((_, reject) => {
      setTimeout(() => reject(new Error(`Check timed out after ${ms}ms`)), ms);
    });
  }
}

interface HealthCheck {
  timeout: number;
  run(): Promise<CheckResult>;
}
```

---

## Individual Checks

### Database Check

```typescript
class DatabaseCheck implements HealthCheck {
  timeout = 5000;
  
  async run(): Promise<CheckResult> {
    const db = getDatabase();
    
    // Test query
    const start = Date.now();
    await db.get('SELECT 1');
    const latency = Date.now() - start;
    
    // Get stats
    const stats = await db.get(`
      SELECT 
        (SELECT COUNT(*) FROM sessions) as sessions,
        (SELECT COUNT(*) FROM messages) as messages
    `);
    
    return {
      status: latency < 1000 ? 'healthy' : 'degraded',
      latency,
      details: {
        sessions: stats.sessions,
        messages: stats.messages
      }
    };
  }
}
```

### Venice API Check

```typescript
class VeniceApiCheck implements HealthCheck {
  timeout = 10000;
  
  async run(): Promise<CheckResult> {
    const balance = await getBalance();
    
    let status: CheckResult['status'] = 'healthy';
    const details: Record<string, unknown> = {
      balanceDiem: balance.diem,
      balanceUsd: balance.usd,
      rateLimit: balance.rateLimit
    };
    
    // Check balance
    if (balance.diem < 1) {
      status = 'unhealthy';
      details.warning = 'Balance critically low';
    } else if (balance.diem < 10) {
      status = 'degraded';
      details.warning = 'Balance low';
    }
    
    // Check rate limit
    if (balance.rateLimit.remaining < 5) {
      status = status === 'healthy' ? 'degraded' : status;
      details.warning = 'Rate limit nearly exhausted';
    }
    
    return { status, details };
  }
}
```

### Memory Check

```typescript
class MemoryCheck implements HealthCheck {
  timeout = 1000;
  
  async run(): Promise<CheckResult> {
    const usage = process.memoryUsage();
    const percentUsed = (usage.heapUsed / usage.heapTotal) * 100;
    
    let status: CheckResult['status'] = 'healthy';
    if (percentUsed > 90) {
      status = 'unhealthy';
    } else if (percentUsed > 75) {
      status = 'degraded';
    }
    
    return {
      status,
      details: {
        heapUsed: usage.heapUsed,
        heapTotal: usage.heapTotal,
        external: usage.external,
        percentUsed: Math.round(percentUsed)
      }
    };
  }
}
```

### WebSocket Check

```typescript
class WebSocketCheck implements HealthCheck {
  timeout = 1000;
  
  async run(): Promise<CheckResult> {
    const wsManager = getWebSocketManager();
    const stats = wsManager.getStats();
    
    return {
      status: 'healthy',
      details: {
        activeConnections: stats.activeConnections,
        messagesPerMinute: stats.messagesPerMinute,
        averageLatency: stats.averageLatency
      }
    };
  }
}
```

---

## Express Routes

```typescript
// bridge/src/health/routes.ts

import { Router } from 'express';

export function healthRoutes(healthService: HealthService): Router {
  const router = Router();
  
  // Basic liveness - is the server running?
  router.get('/health/live', (req, res) => {
    res.json({ status: 'ok' });
  });
  
  // Readiness - is the server ready to handle requests?
  router.get('/health/ready', async (req, res) => {
    const health = await healthService.getHealth(false);
    const status = health.status === 'healthy' ? 200 : 503;
    res.status(status).json(health);
  });
  
  // Simple health
  router.get('/health', async (req, res) => {
    const health = await healthService.getHealth(false);
    const status = health.status === 'healthy' ? 200 : 503;
    res.status(status).json(health);
  });
  
  // Detailed health
  router.get('/health/detailed', async (req, res) => {
    const health = await healthService.getHealth(true);
    const status = health.status === 'healthy' ? 200 : 503;
    res.status(status).json(health);
  });
  
  return router;
}
```

---

## Frontend Health Display

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  SYSTEM STATUS                                              ● All Healthy   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ COMPONENTS ──────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ● Bridge Server      Healthy       Uptime: 2h 34m       Latency: 5ms │ │
│  │  ● Database           Healthy       Sessions: 45         Messages: 1.2K│ │
│  │  ● WebSocket          Healthy       Connections: 3       45 msg/min   │ │
│  │  ● Venice API         Healthy       Balance: 42.5 Diem   Rate: 95/100 │ │
│  │  ● Memory             Healthy       52MB / 100MB (52%)               │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  Last checked: 5 seconds ago                              [Refresh]        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Kubernetes Probes

```yaml
# kubernetes deployment
spec:
  containers:
    - name: sidepanel-bridge
      livenessProbe:
        httpGet:
          path: /health/live
          port: 3000
        initialDelaySeconds: 10
        periodSeconds: 10
      readinessProbe:
        httpGet:
          path: /health/ready
          port: 3000
        initialDelaySeconds: 5
        periodSeconds: 5
```

---

## Related Specifications

- `38-LOGGING-MONITORING.md` - Logging system
- `82-DEBUG-MODE.md` - Debug tools
- `30-BRIDGE-ARCHITECTURE.md` - Bridge design

---

*"Know your system's health before your users do."*
