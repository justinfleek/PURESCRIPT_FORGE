-- | OpenTelemetry Distributed Tracing
module Bridge.Tracing.OpenTelemetry where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe)
import Bridge.Logging.Structured (CorrelationId)

-- | Opaque Tracer type
foreign import data Tracer :: Type

-- | Opaque Span type
foreign import data Span :: Type

-- | Span context for propagation
type SpanContext =
  { traceId :: String
  , spanId :: String
  , traceFlags :: Int
  }

-- | FFI implementations
foreign import createTracerImpl :: String -> String -> Effect Tracer
foreign import startSpanImpl :: Tracer -> String -> Maybe SpanContext -> Effect Span
foreign import endSpanImpl :: Span -> Effect Unit
foreign import setAttributeImpl :: Span -> String -> String -> Effect Unit
foreign import addEventImpl :: Span -> String -> String -> Effect Unit
foreign import getSpanContextImpl :: Span -> Effect SpanContext
foreign import injectTraceContextImpl :: SpanContext -> Effect (Array { key :: String, value :: String })
foreign import extractTraceContextImpl :: Array { key :: String, value :: String } -> Effect (Maybe SpanContext)

-- | Create a tracer with service name and version
createTracer :: String -> String -> Effect Tracer
createTracer = createTracerImpl

-- | Start a new span with optional parent context
startSpan :: Tracer -> String -> Maybe SpanContext -> Effect Span
startSpan = startSpanImpl

-- | End and record a span
endSpan :: Span -> Effect Unit
endSpan = endSpanImpl

-- | Add a key-value attribute to a span
setAttribute :: Span -> String -> String -> Effect Unit
setAttribute = setAttributeImpl

-- | Add a named event with attributes (JSON string) to a span
addEvent :: Span -> String -> String -> Effect Unit
addEvent = addEventImpl

-- | Extract span context for propagation
getSpanContext :: Span -> Effect SpanContext
getSpanContext = getSpanContextImpl

-- | Convert span context to HTTP headers for propagation
injectTraceContext :: SpanContext -> Effect (Array { key :: String, value :: String })
injectTraceContext = injectTraceContextImpl

-- | Parse span context from HTTP headers
extractTraceContext :: Array { key :: String, value :: String } -> Effect (Maybe SpanContext)
extractTraceContext = extractTraceContextImpl
