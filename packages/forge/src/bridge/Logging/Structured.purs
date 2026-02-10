-- | Structured Logging with Correlation IDs
module Bridge.Logging.Structured where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe(..))
import Bridge.FFI.Node.Pino as Pino

-- | Correlation ID for request tracing
type CorrelationId = String

-- | Structured logger with correlation context
type StructuredLogger =
  { baseLogger :: Pino.Logger
  , correlationId :: CorrelationId
  }

-- | FFI for UUID generation
foreign import generateUUID :: Effect String

-- | FFI for logging with level and correlation
foreign import logWithLevel :: StructuredLogger -> String -> String -> Maybe String -> Effect Unit

-- | FFI for creating a child logger
foreign import createChildLogger :: Pino.Logger -> String -> Effect Pino.Logger

-- | Generate a new correlation ID
generateCorrelationId :: Effect CorrelationId
generateCorrelationId = generateUUID

-- | Create a structured logger with optional correlation ID
createStructuredLogger :: Pino.Logger -> Maybe CorrelationId -> Effect StructuredLogger
createStructuredLogger logger mCorrId = do
  corrId <- case mCorrId of
    Just id -> pure id
    Nothing -> generateCorrelationId
  pure { baseLogger: logger, correlationId: corrId }

-- | Log info with correlation
info :: StructuredLogger -> String -> Maybe String -> Effect Unit
info logger msg = logWithLevel logger "info" msg

-- | Log error with correlation
error :: StructuredLogger -> String -> Maybe String -> Effect Unit
error logger msg = logWithLevel logger "error" msg

-- | Log warning with correlation
warn :: StructuredLogger -> String -> Maybe String -> Effect Unit
warn logger msg = logWithLevel logger "warn" msg

-- | Log debug with correlation
debug :: StructuredLogger -> String -> Maybe String -> Effect Unit
debug logger msg = logWithLevel logger "debug" msg

-- | Create a child logger with additional context
child :: StructuredLogger -> String -> Effect StructuredLogger
child logger context = do
  childBase <- createChildLogger logger.baseLogger context
  pure { baseLogger: childBase, correlationId: logger.correlationId }
