-- | Structured Logging - Correlation IDs and Structured Logging
-- |
-- | **What:** Provides structured logging with correlation IDs for request tracing.
-- |         All log entries include correlation ID, timestamp, level, and structured data.
-- | **Why:** Enables distributed tracing and debugging. Correlation IDs allow tracking
-- |         requests across services. Structured logs enable efficient querying and analysis.
-- | **How:** Generates unique correlation IDs for each request. Includes correlation ID
-- |         in all log entries. Uses Pino for structured JSON logging.
-- |
-- | **Dependencies:**
-- | - `Bridge.FFI.Node.Pino`: Pino logger
-- | - `Effect.Random`: Correlation ID generation
-- |
-- | **Mathematical Foundation:**
-- | - **Correlation ID:** Unique identifier per request: `UUID`
-- | - **Log Entry:** `{ correlationId, timestamp, level, message, data }`
-- | - **Trace Invariant:** All logs for a request share the same correlation ID
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Logging.Structured as Logging
-- |
-- | -- Create logger with correlation ID
-- | logger <- Logging.createLoggerWithCorrelation correlationId baseLogger
-- |
-- | -- Log with structured data
-- | Logging.info logger "Request received" { method: "GET", path: "/api/venice" }
-- | ```
module Bridge.Logging.Structured where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Bridge.FFI.Node.Pino (Logger)

-- | FFI: Generate UUID
foreign import generateUUID :: Effect String

-- | FFI: Log with level
foreign import logWithLevel :: StructuredLogger -> String -> String -> Maybe String -> Effect Unit

-- | FFI: Create child logger
foreign import createChildLogger :: Logger -> String -> Effect Logger

-- | Correlation ID (unique per request)
type CorrelationId = String

-- | Structured logger with correlation ID
type StructuredLogger =
  { baseLogger :: Logger
  , correlationId :: CorrelationId
  }

-- | Generate correlation ID
-- |
-- | **Purpose:** Generates a unique correlation ID for request tracing.
-- | **Returns:** Correlation ID string (UUID format)
generateCorrelationId :: Effect CorrelationId
generateCorrelationId = generateUUID

-- | Create structured logger
-- |
-- | **Purpose:** Creates a structured logger with correlation ID.
-- | **Parameters:**
-- | - `baseLogger`: Base Pino logger
-- | - `correlationId`: Correlation ID (or generate new)
-- | **Returns:** Structured logger
createStructuredLogger :: Logger -> Maybe CorrelationId -> Effect StructuredLogger
createStructuredLogger baseLogger maybeCorrelationId = do
  correlationId <- case maybeCorrelationId of
    Just id -> pure id
    Nothing -> generateCorrelationId
  pure { baseLogger, correlationId }

-- | Log info message
-- |
-- | **Purpose:** Logs info-level message with correlation ID and structured data.
-- | **Parameters:**
-- | - `logger`: Structured logger
-- | - `message`: Log message
-- | - `extraData`: Structured data (optional)
info :: StructuredLogger -> String -> Maybe String -> Effect Unit
info logger message extraData = logWithLevel logger "info" message extraData

-- | Log error message
logError :: StructuredLogger -> String -> Maybe String -> Effect Unit
logError logger message extraData = logWithLevel logger "error" message extraData

-- | Log warning message
warn :: StructuredLogger -> String -> Maybe String -> Effect Unit
warn logger message extraData = logWithLevel logger "warn" message extraData

-- | Log debug message
debug :: StructuredLogger -> String -> Maybe String -> Effect Unit
debug logger message extraData = logWithLevel logger "debug" message extraData

-- | Create child logger with additional context
-- |
-- | **Purpose:** Creates a child logger with additional context fields.
-- | **Parameters:**
-- | - `logger`: Parent structured logger
-- | - `context`: Additional context data (JSON string)
-- | **Returns:** Child structured logger
child :: StructuredLogger -> String -> Effect StructuredLogger
child logger context = do
  childLogger <- createChildLogger logger.baseLogger context
  pure { baseLogger: childLogger, correlationId: logger.correlationId }
