# 80-ERROR-TAXONOMY: Error Types, Codes, and Messages

## Overview

Consistent error handling across all layers ensures debuggability and good user experience. This document defines all error types and handling patterns.

---

## Error Categories

### Category 1: Network Errors (1xxx)

| Code | Name | Message | Recovery |
|------|------|---------|----------|
| 1001 | `NETWORK_UNREACHABLE` | "Unable to reach Venice API" | Retry with backoff |
| 1002 | `CONNECTION_TIMEOUT` | "Request timed out" | Retry once |
| 1003 | `CONNECTION_REFUSED` | "Connection refused" | Check if service running |
| 1004 | `SSL_ERROR` | "SSL certificate error" | Check system time |
| 1005 | `DNS_FAILURE` | "DNS lookup failed" | Check network |

### Category 2: Authentication Errors (2xxx)

| Code | Name | Message | Recovery |
|------|------|---------|----------|
| 2001 | `INVALID_API_KEY` | "Invalid Venice API key" | Prompt for new key |
| 2002 | `API_KEY_EXPIRED` | "API key has expired" | Regenerate key |
| 2003 | `INSUFFICIENT_PERMISSIONS` | "API key lacks permissions" | Check key scope |
| 2004 | `SESSION_EXPIRED` | "Session has expired" | Re-authenticate |
| 2005 | `TOKEN_INVALID` | "Invalid authentication token" | Re-authenticate |

### Category 3: Rate Limit Errors (3xxx)

| Code | Name | Message | Recovery |
|------|------|---------|----------|
| 3001 | `RATE_LIMITED_REQUESTS` | "Too many requests" | Wait and retry |
| 3002 | `RATE_LIMITED_TOKENS` | "Token limit exceeded" | Wait for reset |
| 3003 | `DAILY_LIMIT_REACHED` | "Daily request limit reached" | Wait for reset |
| 3004 | `BALANCE_DEPLETED` | "Diem balance depleted" | Wait for reset |

### Category 4: Validation Errors (4xxx)

| Code | Name | Message | Recovery |
|------|------|---------|----------|
| 4001 | `INVALID_JSON` | "Invalid JSON format" | Fix request |
| 4002 | `MISSING_FIELD` | "Required field missing: {field}" | Add field |
| 4003 | `INVALID_TYPE` | "Invalid type for {field}" | Fix type |
| 4004 | `VALUE_OUT_OF_RANGE` | "{field} must be between {min} and {max}" | Fix value |
| 4005 | `MESSAGE_TOO_LARGE` | "Message exceeds size limit" | Reduce size |

### Category 5: WebSocket Errors (5xxx)

| Code | Name | Message | Recovery |
|------|------|---------|----------|
| 5001 | `WS_CONNECTION_FAILED` | "WebSocket connection failed" | Retry connect |
| 5002 | `WS_DISCONNECTED` | "WebSocket disconnected" | Auto-reconnect |
| 5003 | `WS_MESSAGE_FAILED` | "Failed to send message" | Queue and retry |
| 5004 | `WS_AUTH_REQUIRED` | "Authentication required" | Send auth |
| 5005 | `WS_PROTOCOL_ERROR` | "Protocol error" | Reconnect |

### Category 6: Lean4 Errors (6xxx)

| Code | Name | Message | Recovery |
|------|------|---------|----------|
| 6001 | `LEAN_NOT_CONNECTED` | "Lean LSP not connected" | Check installation |
| 6002 | `LEAN_PARSE_ERROR` | "Lean parse error" | Fix syntax |
| 6003 | `LEAN_TYPE_ERROR` | "Type mismatch" | Fix types |
| 6004 | `LEAN_TACTIC_FAILED` | "Tactic failed" | Try different tactic |
| 6005 | `LEAN_TIMEOUT` | "Lean operation timed out" | Simplify proof |

### Category 7: Storage Errors (7xxx)

| Code | Name | Message | Recovery |
|------|------|---------|----------|
| 7001 | `STORAGE_FULL` | "Storage quota exceeded" | Clear old data |
| 7002 | `STORAGE_CORRUPTED` | "Storage data corrupted" | Reset storage |
| 7003 | `SNAPSHOT_NOT_FOUND` | "Snapshot not found" | Select different |
| 7004 | `SESSION_NOT_FOUND` | "Session not found" | Start new |
| 7005 | `PERMISSION_DENIED` | "Storage permission denied" | Check permissions |

### Category 8: Internal Errors (9xxx)

| Code | Name | Message | Recovery |
|------|------|---------|----------|
| 9001 | `INTERNAL_ERROR` | "Internal error occurred" | Report bug |
| 9002 | `UNEXPECTED_STATE` | "Unexpected state" | Restart |
| 9003 | `ASSERTION_FAILED` | "Assertion failed" | Report bug |
| 9004 | `NOT_IMPLEMENTED` | "Feature not implemented" | Wait for update |

---

## Error Structure

### TypeScript Definition

```typescript
interface AppError {
  code: number;
  name: string;
  message: string;
  details?: Record<string, unknown>;
  recoverable: boolean;
  timestamp: Date;
  stack?: string;
}

class SidepanelError extends Error {
  constructor(
    public code: number,
    public name: string,
    message: string,
    public details?: Record<string, unknown>,
    public recoverable: boolean = true
  ) {
    super(message);
    this.timestamp = new Date();
  }
  
  static fromCode(code: number, details?: Record<string, unknown>): SidepanelError {
    const def = ERROR_DEFINITIONS[code];
    return new SidepanelError(
      code,
      def.name,
      interpolateMessage(def.message, details),
      details,
      def.recoverable
    );
  }
  
  toJSON(): AppError {
    return {
      code: this.code,
      name: this.name,
      message: this.message,
      details: this.details,
      recoverable: this.recoverable,
      timestamp: this.timestamp
    };
  }
}
```

### PureScript Definition

```purescript
module Sidepanel.Error where

import Data.Maybe (Maybe)
import Data.DateTime (DateTime)

type ErrorDetails = Map String Json

data ErrorCode
  = NetworkUnreachable
  | ConnectionTimeout
  | InvalidApiKey
  | RateLimited
  | ValidationFailed String
  | WebSocketDisconnected
  | LeanNotConnected
  | InternalError
  -- ... more

data AppError = AppError
  { code :: Int
  , name :: String
  , message :: String
  , details :: Maybe ErrorDetails
  , recoverable :: Boolean
  , timestamp :: DateTime
  }

-- | Check if error is recoverable
isRecoverable :: AppError -> Boolean
isRecoverable = _.recoverable

-- | Get retry delay for recoverable errors
getRetryDelay :: AppError -> Maybe Milliseconds
getRetryDelay err
  | not (isRecoverable err) = Nothing
  | err.code >= 3000 && err.code < 4000 = Just (Milliseconds 60000.0)
  | err.code >= 1000 && err.code < 2000 = Just (Milliseconds 5000.0)
  | otherwise = Just (Milliseconds 1000.0)
```

---

## Error Handling Patterns

### Bridge Server

```typescript
// Global error handler
app.use((error: Error, req: Request, res: Response, next: NextFunction) => {
  if (error instanceof SidepanelError) {
    logError(error);
    res.status(getHttpStatus(error.code)).json(error.toJSON());
  } else {
    // Unexpected error - don't leak details
    const internal = SidepanelError.fromCode(9001);
    logError(error); // Log full error internally
    res.status(500).json(internal.toJSON());
  }
});

// Map error codes to HTTP status
function getHttpStatus(code: number): number {
  if (code >= 2000 && code < 3000) return 401;
  if (code >= 3000 && code < 4000) return 429;
  if (code >= 4000 && code < 5000) return 400;
  if (code >= 9000) return 500;
  return 500;
}
```

### WebSocket Messages

```typescript
// Error response format
interface ErrorResponse {
  jsonrpc: '2.0';
  id: number | null;
  error: {
    code: number;
    message: string;
    data?: AppError;
  };
}

function sendError(ws: WebSocket, id: number | null, error: SidepanelError): void {
  ws.send(JSON.stringify({
    jsonrpc: '2.0',
    id,
    error: {
      code: error.code,
      message: error.message,
      data: error.toJSON()
    }
  }));
}
```

### PureScript Components

```purescript
-- Error boundary component
errorBoundary :: forall q i o m. MonadAff m => H.Component q i o m -> H.Component q i o m
errorBoundary child = H.mkComponent
  { initialState: \input -> { error: Nothing, childInput: input }
  , render: \state -> case state.error of
      Nothing -> HH.slot _child unit child state.childInput HandleChild
      Just err -> renderError err
  , eval: H.mkEval $ H.defaultEval
      { handleAction = case _ of
          HandleChild output -> H.raise output
          ClearError -> H.modify_ _ { error = Nothing }
          CatchError err -> H.modify_ _ { error = Just err }
      }
  }

renderError :: forall m. AppError -> H.ComponentHTML Action () m
renderError err =
  HH.div
    [ HP.class_ (H.ClassName "error-display") ]
    [ HH.h3_ [ HH.text "Something went wrong" ]
    , HH.p_ [ HH.text err.message ]
    , if err.recoverable
        then HH.button
          [ HE.onClick \_ -> ClearError ]
          [ HH.text "Try Again" ]
        else HH.text ""
    ]
```

---

## User-Facing Messages

### Message Guidelines

1. **Be specific:** "Invalid API key" not "Authentication failed"
2. **Be actionable:** Include what user can do
3. **Be honest:** Don't hide errors, explain them
4. **Be human:** Use natural language, not codes

### Message Templates

```typescript
const USER_MESSAGES: Record<number, string> = {
  // Network
  1001: "Can't reach Venice API. Please check your internet connection.",
  1002: "Request took too long. Trying again...",
  
  // Auth
  2001: "Your API key doesn't appear to be valid. Please check it in settings.",
  2004: "Your session has expired. Please reconnect.",
  
  // Rate limits
  3001: "Slow down! Venice is rate limiting requests. Waiting...",
  3004: "You've used all your Diem for today. Resets at midnight UTC.",
  
  // Validation
  4001: "Received invalid data. This might be a bug.",
  
  // WebSocket
  5002: "Lost connection to sidepanel. Reconnecting...",
  
  // Lean
  6001: "Lean language server isn't connected. Check your Lean installation.",
  6003: "Type error in proof. Check the highlighted line.",
  
  // Storage
  7001: "Storage is full. Consider clearing old sessions.",
  
  // Internal
  9001: "Something unexpected happened. Please report this bug."
};

function getUserMessage(error: AppError): string {
  return USER_MESSAGES[error.code] ?? error.message;
}
```

---

## Recovery Actions

### Automatic Recovery

```typescript
async function withAutoRecovery<T>(
  operation: () => Promise<T>,
  options: RecoveryOptions = {}
): Promise<T> {
  const { maxRetries = 3, baseDelay = 1000 } = options;
  
  for (let attempt = 0; attempt <= maxRetries; attempt++) {
    try {
      return await operation();
    } catch (error) {
      if (!(error instanceof SidepanelError) || !error.recoverable) {
        throw error;
      }
      
      if (attempt === maxRetries) {
        throw error;
      }
      
      const delay = baseDelay * Math.pow(2, attempt);
      await sleep(delay);
    }
  }
  
  throw new Error('Unreachable');
}
```

### User-Initiated Recovery

```purescript
-- Actions user can take to recover
data RecoveryAction
  = Retry
  | ReAuthenticate
  | ClearStorage
  | Reconnect
  | OpenSettings
  | ReportBug

getRecoveryActions :: AppError -> Array RecoveryAction
getRecoveryActions err
  | err.code >= 1000 && err.code < 2000 = [Retry, OpenSettings]
  | err.code >= 2000 && err.code < 3000 = [ReAuthenticate, OpenSettings]
  | err.code >= 3000 && err.code < 4000 = [Retry]  -- After waiting
  | err.code >= 5000 && err.code < 6000 = [Reconnect]
  | err.code >= 7000 && err.code < 8000 = [ClearStorage]
  | otherwise = [ReportBug]
```

---

## Logging Errors

```typescript
interface ErrorLog {
  timestamp: string;
  error: AppError;
  context: {
    component: string;
    action?: string;
    userId?: string;
  };
}

function logError(error: AppError, context: Partial<ErrorLog['context']> = {}): void {
  const log: ErrorLog = {
    timestamp: new Date().toISOString(),
    error,
    context: {
      component: context.component ?? 'unknown',
      ...context
    }
  };
  
  // Never log sensitive data
  const sanitized = sanitizeLog(log);
  
  if (error.code >= 9000) {
    // Internal errors get full stack trace
    console.error(JSON.stringify(sanitized, null, 2));
  } else {
    console.warn(JSON.stringify(sanitized));
  }
}
```

---

## Related Specifications

- `81-LOGGING-STRATEGY.md` - Structured logging
- `17-VENICE-ERROR-HANDLING.md` - Venice-specific errors
- `67-LEAN4-ERROR-HANDLING.md` - Lean4-specific errors

---

*"Good error handling is invisible to users—until they need it."*
