# 76-LOAD-TESTING: Performance and Stress Testing

## Overview

Load testing ensures the sidepanel performs well under realistic and extreme conditions. This document covers test scenarios, tools, and benchmarks.

---

## Performance Targets

| Metric | Target | Maximum |
|--------|--------|---------|
| WebSocket latency | <50ms p50 | <200ms p99 |
| State update | <100ms | <500ms |
| Initial load | <1s | <3s |
| Memory usage | <100MB | <256MB |
| Concurrent sessions | 10 | 50 |
| Messages/second | 100 | 500 |

---

## Test Scenarios

### 1. Normal Usage

Simulates typical user behavior:
- 1 active session
- 50 messages over 30 minutes
- Occasional file context updates
- Regular balance checks

```typescript
// test/load/normal-usage.ts
export const normalUsage: LoadScenario = {
  name: 'Normal Usage',
  duration: '30m',
  users: 1,
  actions: [
    { type: 'connect', weight: 1 },
    { type: 'sendMessage', weight: 10, delay: '30s-2m' },
    { type: 'updateContext', weight: 2, delay: '5m-10m' },
    { type: 'getBalance', weight: 5, delay: '1m' },
    { type: 'createSnapshot', weight: 1, delay: '10m' }
  ]
};
```

### 2. Heavy Session

Single user with intense activity:
- 200+ messages
- Large file context (50+ files)
- Frequent tool calls
- Multiple branches

```typescript
export const heavySession: LoadScenario = {
  name: 'Heavy Session',
  duration: '15m',
  users: 1,
  actions: [
    { type: 'sendMessage', weight: 20, delay: '5s-30s' },
    { type: 'toolCall', weight: 15, delay: '10s-1m' },
    { type: 'addFile', weight: 5, delay: '1m' },
    { type: 'createBranch', weight: 1, delay: '5m' }
  ],
  setup: {
    initialFiles: 30,
    initialMessages: 50
  }
};
```

### 3. Concurrent Users

Multiple simultaneous connections:
- 10-50 concurrent users
- Mixed activity patterns
- Shared resource contention

```typescript
export const concurrentUsers: LoadScenario = {
  name: 'Concurrent Users',
  duration: '10m',
  users: 25,
  rampUp: '2m',
  actions: [
    { type: 'connect', weight: 1 },
    { type: 'sendMessage', weight: 10, delay: '30s-2m' },
    { type: 'getBalance', weight: 5, delay: '30s' }
  ]
};
```

### 4. Stress Test

Push system to limits:
- Maximum connections
- Rapid message bursts
- Large payloads
- Memory pressure

```typescript
export const stressTest: LoadScenario = {
  name: 'Stress Test',
  duration: '5m',
  users: 50,
  rampUp: '30s',
  actions: [
    { type: 'sendMessage', weight: 50, delay: '100ms-1s' },
    { type: 'largePayload', weight: 5, delay: '5s' }
  ],
  thresholds: {
    maxLatency: '1s',
    maxErrors: '1%'
  }
};
```

### 5. Endurance Test

Long-running stability:
- 24-hour duration
- Moderate constant load
- Memory leak detection
- Connection stability

```typescript
export const enduranceTest: LoadScenario = {
  name: 'Endurance Test',
  duration: '24h',
  users: 5,
  actions: [
    { type: 'sendMessage', weight: 10, delay: '1m-5m' },
    { type: 'getBalance', weight: 2, delay: '5m' }
  ],
  monitoring: {
    memoryInterval: '5m',
    alertOnGrowth: '10%/hour'
  }
};
```

---

## Load Testing Tools

### k6 Configuration

```javascript
// k6/websocket-load.js
import ws from 'k6/ws';
import { check } from 'k6';

export const options = {
  stages: [
    { duration: '2m', target: 10 },   // Ramp up
    { duration: '5m', target: 10 },   // Sustain
    { duration: '2m', target: 25 },   // Increase
    { duration: '5m', target: 25 },   // Sustain
    { duration: '2m', target: 0 }     // Ramp down
  ],
  thresholds: {
    'ws_connecting': ['p(95)<500'],
    'ws_msgs_received': ['rate>10'],
    'checks': ['rate>0.99']
  }
};

export default function() {
  const url = 'ws://localhost:3000/ws';
  
  const response = ws.connect(url, {}, (socket) => {
    socket.on('open', () => {
      // Send ping
      socket.send(JSON.stringify({
        jsonrpc: '2.0',
        method: 'ping',
        id: Date.now()
      }));
    });
    
    socket.on('message', (msg) => {
      const data = JSON.parse(msg);
      check(data, {
        'has result': (d) => d.result !== undefined || d.method !== undefined
      });
    });
    
    socket.setTimeout(() => {
      socket.close();
    }, 10000);
  });
  
  check(response, {
    'connected successfully': (r) => r && r.status === 101
  });
}
```

### Artillery Configuration

```yaml
# artillery/load-test.yml
config:
  target: 'ws://localhost:3000'
  phases:
    - duration: 120
      arrivalRate: 5
      name: "Warm up"
    - duration: 300
      arrivalRate: 10
      name: "Sustained load"
    - duration: 120
      arrivalRate: 20
      name: "Peak load"

scenarios:
  - name: "WebSocket session"
    engine: ws
    flow:
      - send:
          json:
            jsonrpc: "2.0"
            method: "ping"
            id: "{{ $randomNumber(1, 10000) }}"
      - think: 1
      - send:
          json:
            jsonrpc: "2.0"
            method: "balance.get"
            id: "{{ $randomNumber(1, 10000) }}"
      - think: 5
      - loop:
          - send:
              json:
                jsonrpc: "2.0"
                method: "session.message"
                params:
                  content: "Test message {{ $loopCount }}"
                id: "{{ $randomNumber(1, 10000) }}"
          - think: 2
        count: 10
```

---

## Running Load Tests

```bash
# k6 tests
k6 run k6/websocket-load.js

# With HTML report
k6 run --out json=results.json k6/websocket-load.js
k6-reporter results.json

# Artillery tests
artillery run artillery/load-test.yml

# With report
artillery run --output report.json artillery/load-test.yml
artillery report report.json
```

---

## Metrics Collection

### Key Metrics

```typescript
interface LoadTestMetrics {
  // Latency
  latencyP50: number;
  latencyP95: number;
  latencyP99: number;
  
  // Throughput
  requestsPerSecond: number;
  messagesPerSecond: number;
  
  // Errors
  errorRate: number;
  connectionFailures: number;
  
  // Resources
  cpuUsage: number;
  memoryUsage: number;
  openConnections: number;
  
  // Custom
  balanceUpdatesPerSecond: number;
  stateUpdatesPerSecond: number;
}
```

### Grafana Dashboard

```json
{
  "dashboard": {
    "title": "Load Test Metrics",
    "panels": [
      {
        "title": "Request Latency",
        "type": "graph",
        "targets": [
          { "expr": "histogram_quantile(0.50, ws_latency_bucket)" },
          { "expr": "histogram_quantile(0.95, ws_latency_bucket)" },
          { "expr": "histogram_quantile(0.99, ws_latency_bucket)" }
        ]
      },
      {
        "title": "Throughput",
        "type": "graph",
        "targets": [
          { "expr": "rate(ws_messages_total[1m])" }
        ]
      },
      {
        "title": "Active Connections",
        "type": "stat",
        "targets": [
          { "expr": "ws_active_connections" }
        ]
      }
    ]
  }
}
```

---

## Benchmark Results

### Baseline Performance

| Scenario | Latency p50 | Latency p99 | Errors |
|----------|-------------|-------------|--------|
| Normal Usage | 12ms | 45ms | 0% |
| Heavy Session | 25ms | 120ms | 0.1% |
| 25 Concurrent | 35ms | 180ms | 0.2% |
| Stress (50 users) | 85ms | 450ms | 1.2% |

### Resource Usage

| Scenario | CPU | Memory | Connections |
|----------|-----|--------|-------------|
| Idle | 1% | 45MB | 0 |
| Normal | 5% | 65MB | 1 |
| Heavy | 15% | 120MB | 1 |
| 25 Concurrent | 35% | 180MB | 25 |
| Stress | 75% | 220MB | 50 |

---

## Related Specifications

- `67-PERFORMANCE-PROFILER.md` - Runtime profiling
- `39-HEALTH-CHECKS.md` - Health monitoring
- `70-TESTING-STRATEGY.md` - Testing overview

---

*"Test at scale before your users do."*
