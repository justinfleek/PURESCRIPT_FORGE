# 83-SECURITY-MODEL: Threat Analysis and Mitigations

## Overview

Security is critical for a tool that handles API keys and code. This document outlines the threat model, attack vectors, and mitigations.

---

## Trust Boundaries

```
┌─────────────────────────────────────────────────────────────────────┐
│                      TRUST BOUNDARY 1: User's Machine               │
│                                                                      │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │                 TRUST BOUNDARY 2: Bridge Process               │ │
│  │                                                                 │ │
│  │  • Venice API key (encrypted at rest)                          │ │
│  │  • Session data                                                │ │
│  │  • All network communication                                   │ │
│  │                                                                 │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                      │
│  Browser (localhost only) ──── WebSocket ──── Bridge                │
│  Terminal (OpenCode) ──────── Plugin ─────── Bridge                 │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
                                    │
                                    │ HTTPS
                                    ▼
                           ┌─────────────────┐
                           │ TRUST BOUNDARY 3│
                           │ External APIs   │
                           │ - Venice AI     │
                           │ - Lean LSP      │
                           └─────────────────┘
```

---

## Threat Analysis

### T1: API Key Theft

**Attack:** Attacker obtains Venice API key
**Impact:** Unauthorized API usage, cost to victim
**Likelihood:** Medium
**Mitigation:**
- Store keys in system keychain (macOS Keychain, GNOME Keyring)
- Never log keys
- Never send keys to browser
- Memory-only key loading with zeroing

### T2: Man-in-the-Middle

**Attack:** Intercept Bridge ↔ Venice communication
**Impact:** Key theft, data manipulation
**Likelihood:** Low (HTTPS)
**Mitigation:**
- HTTPS only for external APIs
- Certificate validation
- No certificate override options

### T3: WebSocket Hijacking

**Attack:** Malicious code connects to Bridge WebSocket
**Impact:** Session hijacking, false data injection
**Likelihood:** Medium
**Mitigation:**
- localhost binding only
- Session token authentication
- Origin validation
- Rate limiting

### T4: Session Data Leakage

**Attack:** Session storage compromised
**Impact:** Conversation/code exposure
**Likelihood:** Low
**Mitigation:**
- Encrypted at rest (AES-256-GCM)
- User-controlled encryption key
- Optional session clearing

### T5: Plugin Sandbox Escape

**Attack:** Malicious plugin code escapes OpenCode sandbox
**Impact:** Full system access
**Likelihood:** Low (depends on OpenCode)
**Mitigation:**
- Minimal plugin permissions
- No shell execution
- Audit plugin code

### T6: XSS in Browser UI

**Attack:** Inject malicious script into sidepanel
**Impact:** Key theft, session hijacking
**Likelihood:** Low (PureScript sanitization)
**Mitigation:**
- Content Security Policy
- No eval/innerHTML
- PureScript's type-safe HTML

### T7: Denial of Service

**Attack:** Flood Bridge with requests
**Impact:** Service unavailable
**Likelihood:** Low (localhost only)
**Mitigation:**
- Rate limiting
- Request size limits
- Connection limits

---

## Security Controls

### API Key Management

```typescript
// Use system keychain
import keytar from 'keytar';

const SERVICE = 'opencode-sidepanel';
const ACCOUNT = 'venice-api-key';

// Store key
async function storeApiKey(key: string): Promise<void> {
  await keytar.setPassword(SERVICE, ACCOUNT, key);
}

// Retrieve key
async function getApiKey(): Promise<string | null> {
  return keytar.getPassword(SERVICE, ACCOUNT);
}

// Delete key
async function deleteApiKey(): Promise<boolean> {
  return keytar.deletePassword(SERVICE, ACCOUNT);
}

// NEVER:
// - Store in environment variables
// - Store in config files
// - Log the key
// - Send to browser
```

### Content Security Policy

```html
<meta http-equiv="Content-Security-Policy" content="
  default-src 'self';
  script-src 'self';
  style-src 'self' 'unsafe-inline';
  connect-src 'self' ws://localhost:8765;
  img-src 'self' data:;
  font-src 'self';
  object-src 'none';
  base-uri 'self';
  form-action 'self';
  frame-ancestors 'none';
">
```

### WebSocket Authentication

```typescript
// Server-side token validation
const validTokens = new Set<string>();

wss.on('connection', (ws, req) => {
  // Check origin
  const origin = req.headers.origin;
  if (origin && !origin.startsWith('http://localhost')) {
    ws.close(4001, 'Invalid origin');
    return;
  }
  
  // Require authentication within 5 seconds
  const authTimeout = setTimeout(() => {
    ws.close(4002, 'Authentication timeout');
  }, 5000);
  
  ws.on('message', (data) => {
    const msg = JSON.parse(data.toString());
    
    if (msg.method === 'auth') {
      if (validTokens.has(msg.params.token)) {
        clearTimeout(authTimeout);
        // Connection authenticated
      } else {
        ws.close(4003, 'Invalid token');
      }
    }
  });
});
```

### Rate Limiting

```typescript
import { RateLimiter } from 'limiter';

// Per-client rate limits
const limiters = new Map<string, RateLimiter>();

function getRateLimiter(clientId: string): RateLimiter {
  if (!limiters.has(clientId)) {
    limiters.set(clientId, new RateLimiter({
      tokensPerInterval: 100,
      interval: 'second'
    }));
  }
  return limiters.get(clientId)!;
}

// Check before processing
async function handleMessage(clientId: string, msg: Message): Promise<void> {
  const limiter = getRateLimiter(clientId);
  
  if (!await limiter.tryRemoveTokens(1)) {
    throw new Error('Rate limit exceeded');
  }
  
  // Process message
}
```

### Input Validation

```typescript
import { z } from 'zod';

// Define schemas for all inputs
const MessageSchema = z.object({
  jsonrpc: z.literal('2.0'),
  id: z.number().optional(),
  method: z.string().max(100),
  params: z.record(z.unknown()).optional()
});

// Validate all incoming messages
function parseMessage(data: unknown): Message {
  return MessageSchema.parse(data);
}

// Size limits
const MAX_MESSAGE_SIZE = 1024 * 1024; // 1MB

ws.on('message', (data) => {
  if (data.length > MAX_MESSAGE_SIZE) {
    ws.close(4004, 'Message too large');
    return;
  }
  
  try {
    const msg = parseMessage(JSON.parse(data.toString()));
    handleMessage(msg);
  } catch (error) {
    ws.send(JSON.stringify({
      jsonrpc: '2.0',
      error: { code: -32700, message: 'Parse error' }
    }));
  }
});
```

---

## Data Protection

### Encryption at Rest

```typescript
import { createCipheriv, createDecipheriv, randomBytes } from 'crypto';

const ALGORITHM = 'aes-256-gcm';
const KEY_LENGTH = 32;
const IV_LENGTH = 16;
const TAG_LENGTH = 16;

interface EncryptedData {
  iv: Buffer;
  tag: Buffer;
  data: Buffer;
}

function encrypt(plaintext: Buffer, key: Buffer): EncryptedData {
  const iv = randomBytes(IV_LENGTH);
  const cipher = createCipheriv(ALGORITHM, key, iv);
  
  const data = Buffer.concat([
    cipher.update(plaintext),
    cipher.final()
  ]);
  
  return {
    iv,
    tag: cipher.getAuthTag(),
    data
  };
}

function decrypt(encrypted: EncryptedData, key: Buffer): Buffer {
  const decipher = createDecipheriv(ALGORITHM, key, encrypted.iv);
  decipher.setAuthTag(encrypted.tag);
  
  return Buffer.concat([
    decipher.update(encrypted.data),
    decipher.final()
  ]);
}
```

### Session Data Handling

```typescript
// Session data is encrypted before storage
interface StoredSession {
  id: string;
  encryptedData: EncryptedData;
  createdAt: Date;
}

// Minimal data retention
// - Clear sessions older than 30 days
// - User can trigger immediate clear
// - No cloud sync (local only)
```

---

## Audit Logging

```typescript
interface SecurityEvent {
  timestamp: Date;
  type: SecurityEventType;
  clientId?: string;
  details: Record<string, unknown>;
}

type SecurityEventType =
  | 'auth.success'
  | 'auth.failure'
  | 'auth.timeout'
  | 'ratelimit.exceeded'
  | 'validation.failed'
  | 'connection.rejected'
  | 'key.accessed'
  | 'key.stored'
  | 'key.deleted';

function logSecurityEvent(event: SecurityEvent): void {
  // Log to secure, append-only log
  // Never include sensitive data in logs
  securityLog.append({
    ...event,
    timestamp: event.timestamp.toISOString()
  });
}

// Redaction for any logged data
function redact(data: unknown): unknown {
  if (typeof data === 'string' && data.startsWith('vk_')) {
    return '[REDACTED API KEY]';
  }
  // ... more redaction rules
}
```

---

## Secure Development Practices

### Dependency Management

```bash
# Regular dependency audits
pnpm audit

# Pin exact versions
# package.json: "ws": "8.14.2" (not "^8.14.2")

# Review dependency changes in PRs
```

### Code Review Security Checklist

- [ ] No hardcoded secrets
- [ ] API key never logged or sent to client
- [ ] Input validation on all external data
- [ ] Output encoding for HTML
- [ ] Rate limiting on new endpoints
- [ ] Error messages don't leak internals

---

## Incident Response

### Key Compromise

1. Immediately revoke key in Venice dashboard
2. Generate new key
3. Store new key in keychain
4. Review audit logs for unauthorized usage
5. Update security practices if needed

### Session Compromise

1. Clear all local session data
2. Regenerate session tokens
3. Force re-authentication
4. Review what data may have been exposed

---

## Related Specifications

- `84-AUTHENTICATION-FLOW.md` - OAuth implementation
- `19-VENICE-AUTHENTICATION.md` - API key handling
- `33-AUDIT-LOGGING.md` - Logging strategy

---

*"Security is not a feature—it's a continuous practice."*
