-- | OpenTelemetry Tracing - Distributed Tracing Support
-- |
-- | **What:** Provides OpenTelemetry-compatible distributed tracing for request
-- |         tracking across services. Creates spans, adds attributes, and propagates
-- |         trace context.
-- | **Why:** Enables end-to-end request tracing across Bridge Server, Venice API,
-- |         PostgreSQL, and Lean LSP. Essential for debugging production issues.
-- | **How:** Creates spans for operations, adds attributes and events, propagates
-- |         trace context via headers. Exports traces to OpenTelemetry collector.
-- |
-- | **Dependencies:**
-- | - Node.js `@opentelemetry/api` (via FFI)
-- | - `Bridge.Logging.Structured`: Correlation IDs
-- |
-- | **Mathematical Foundation:**
-- | - **Trace:** Tree of spans representing request flow
-- | - **Span:** Single operation within a trace
-- | - **Trace Context:** Propagated via headers (traceparent, tracestate)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Tracing.OpenTelemetry as Tracing
-- |
-- | -- Start span
-- | span <- Tracing.startSpan "venice.chat" tracer
-- |
-- | -- Add attribute
-- | Tracing.setAttribute span "model" "gpt-4"
-- |
-- | -- End span
-- | Tracing.endSpan span
-- | ```
module Bridge.Tracing.OpenTelemetry where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Maybe (Maybe(..))
import Bridge.Logging.Structured (CorrelationId)

-- | Opaque Tracer type
foreign import data Tracer :: Type

-- | Opaque Span type
foreign import data Span :: Type

-- | FFI: Create tracer implementation
foreign import createTracerImpl :: String -> String -> Effect Tracer

-- | FFI: Start span implementation
foreign import startSpanImpl :: Tracer -> String -> Maybe SpanContext -> Effect Span

-- | FFI: End span implementation
foreign import endSpanImpl :: Span -> Effect Unit

-- | FFI: Set attribute implementation
foreign import setAttributeImpl :: Span -> String -> String -> Effect Unit

-- | FFI: Add event implementation
foreign import addEventImpl :: Span -> String -> String -> Effect Unit

-- | FFI: Get span context implementation
foreign import getSpanContextImpl :: Span -> Effect SpanContext

-- | FFI: Inject trace context implementation
foreign import injectTraceContextImpl :: SpanContext -> Effect (Array { key :: String, value :: String })

-- | FFI: Extract trace context implementation
foreign import extractTraceContextImpl :: Array { key :: String, value :: String } -> Effect (Maybe SpanContext)

-- | Span context (for propagation)
type SpanContext =
  { traceId :: String
  , spanId :: String
  , traceFlags :: Int
  }

-- | Create tracer
-- |
-- | **Purpose:** Creates an OpenTelemetry tracer instance.
-- | **Parameters:**
-- | - `serviceName`: Service name (e.g., "bridge-server")
-- | - `serviceVersion`: Service version
-- | **Returns:** Tracer instance
createTracer :: String -> String -> Effect Tracer
createTracer serviceName serviceVersion = createTracerImpl serviceName serviceVersion

-- | Start span
-- |
-- | **Purpose:** Starts a new span for an operation.
-- | **Parameters:**
-- | - `tracer`: Tracer instance
-- | - `spanName`: Span name (e.g., "venice.chat")
-- | - `parentContext`: Optional parent span context
-- | **Returns:** Span instance
startSpan :: Tracer -> String -> Maybe SpanContext -> Effect Span
startSpan tracer spanName parentContext = startSpanImpl tracer spanName parentContext

-- | End span
-- |
-- | **Purpose:** Ends a span and records it.
-- | **Parameters:**
-- | - `span`: Span instance
-- | **Side Effects:** Records span to trace exporter
endSpan :: Span -> Effect Unit
endSpan = endSpanImpl

-- | Set span attribute
-- |
-- | **Purpose:** Adds an attribute to a span.
-- | **Parameters:**
-- | - `span`: Span instance
-- | - `key`: Attribute key
-- | - `value`: Attribute value (string)
setAttribute :: Span -> String -> String -> Effect Unit
setAttribute = setAttributeImpl

-- | Add span event
-- |
-- | **Purpose:** Adds an event to a span.
-- | **Parameters:**
-- | - `span`: Span instance
-- | - `eventName`: Event name
-- | - `attributes`: Event attributes (JSON string)
addEvent :: Span -> String -> String -> Effect Unit
addEvent = addEventImpl

-- | Get span context
-- |
-- | **Purpose:** Extracts span context for propagation.
-- | **Parameters:**
-- | - `span`: Span instance
-- | **Returns:** Span context
getSpanContext :: Span -> Effect SpanContext
getSpanContext = getSpanContextImpl

-- | Inject trace context into headers
-- |
-- | **Purpose:** Injects trace context into HTTP headers for propagation.
-- | **Parameters:**
-- | - `spanContext`: Span context
-- | **Returns:** Headers map (key -> value)
injectTraceContext :: SpanContext -> Effect (Array { key :: String, value :: String })
injectTraceContext = injectTraceContextImpl

-- | Extract trace context from headers
-- |
-- | **Purpose:** Extracts trace context from HTTP headers.
-- | **Parameters:**
-- | - `headers`: HTTP headers
-- | **Returns:** Maybe span context
extractTraceContext :: Array { key :: String, value :: String } -> Effect (Maybe SpanContext)
extractTraceContext = extractTraceContextImpl
