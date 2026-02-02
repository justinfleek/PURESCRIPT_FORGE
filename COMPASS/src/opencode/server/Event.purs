{-|
Module      : Opencode.Server.Event
Description : Server-Sent Events (SSE) implementation
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Server Events

SSE event bus for real-time updates to connected clients.
Matches OpenCode's bus/bus-event.ts architecture.

== Coeffect Equation

@
  subscribe   : Handler -> Graded IO Unsubscribe
  subscribeAll: Handler -> Graded IO Unsubscribe
  publish     : Event -> Graded IO Unit
@

== Event Types

@
  session.created   - New session created
  session.updated   - Session metadata changed
  message.updated   - Message content changed
  message.part.updated - Part added/changed
  tool.started      - Tool execution started
  tool.completed    - Tool execution finished
  server.connected  - Client connected to SSE
  server.heartbeat  - Keep-alive ping
@

-}
module Opencode.Server.Event
  ( -- * Types
    Event
  , EventType(..)
  , EventHandler
  , Unsubscribe
    -- * Subscription
  , subscribe
  , subscribeAll
  , unsubscribe
    -- * Publishing
  , publish
  , broadcast
    -- * Event Builders
  , sessionCreated
  , sessionUpdated
  , messageUpdated
  , partUpdated
  , toolStarted
  , toolCompleted
  , serverConnected
  , serverHeartbeat
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Array as Array
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- ════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ════════════════════════════════════════════════════════════════════════════

-- | Event type enum
data EventType
  = SessionCreated
  | SessionUpdated
  | SessionRemoved
  | MessageUpdated
  | MessageRemoved
  | PartUpdated
  | PartRemoved
  | ToolStarted
  | ToolCompleted
  | ToolError
  | PermissionRequested
  | PermissionResponded
  | ServerConnected
  | ServerHeartbeat
  | InstanceDisposed

instance showEventType :: Show EventType where
  show SessionCreated = "session.created"
  show SessionUpdated = "session.updated"
  show SessionRemoved = "session.removed"
  show MessageUpdated = "message.updated"
  show MessageRemoved = "message.removed"
  show PartUpdated = "message.part.updated"
  show PartRemoved = "message.part.removed"
  show ToolStarted = "tool.started"
  show ToolCompleted = "tool.completed"
  show ToolError = "tool.error"
  show PermissionRequested = "permission.requested"
  show PermissionResponded = "permission.responded"
  show ServerConnected = "server.connected"
  show ServerHeartbeat = "server.heartbeat"
  show InstanceDisposed = "instance.disposed"

-- | Event structure
type Event =
  { type :: EventType
  , properties :: EventProperties
  }

-- | Event properties (union of possible property sets)
type EventProperties =
  { sessionID :: Maybe String
  , messageID :: Maybe String
  , partID :: Maybe String
  , toolName :: Maybe String
  , delta :: Maybe String
  }

-- | Empty properties
emptyProperties :: EventProperties
emptyProperties =
  { sessionID: Nothing
  , messageID: Nothing
  , partID: Nothing
  , toolName: Nothing
  , delta: Nothing
  }

-- | Event handler function
type EventHandler = Event -> Effect Unit

-- | Unsubscribe function
type Unsubscribe = Effect Unit

-- | Subscription entry
type Subscription =
  { id :: String
  , handler :: EventHandler
  , filter :: Maybe EventType
  }

-- | Global subscribers ref
foreign import subscribersRef :: Ref (Array Subscription)

-- | Counter for subscription IDs
foreign import counterRef :: Ref Int

-- ════════════════════════════════════════════════════════════════════════════
-- SUBSCRIPTION
-- ════════════════════════════════════════════════════════════════════════════

-- | Subscribe to specific event type
subscribe :: EventType -> EventHandler -> Effect Unsubscribe
subscribe eventType handler = do
  id <- nextId
  let sub = { id, handler, filter: Just eventType }
  Ref.modify_ (Array.cons sub) subscribersRef
  pure $ unsubscribe id

-- | Subscribe to all events
subscribeAll :: EventHandler -> Effect Unsubscribe
subscribeAll handler = do
  id <- nextId
  let sub = { id, handler, filter: Nothing }
  Ref.modify_ (Array.cons sub) subscribersRef
  pure $ unsubscribe id

-- | Unsubscribe by ID
unsubscribe :: String -> Effect Unit
unsubscribe subId =
  Ref.modify_ (Array.filter (\s -> s.id /= subId)) subscribersRef

-- | Get next subscription ID
nextId :: Effect String
nextId = do
  n <- Ref.read counterRef
  Ref.write (n + 1) counterRef
  pure $ "sub_" <> show n

-- ════════════════════════════════════════════════════════════════════════════
-- PUBLISHING
-- ════════════════════════════════════════════════════════════════════════════

-- | Publish event to matching subscribers
publish :: Event -> Effect Unit
publish event = do
  subs <- Ref.read subscribersRef
  _ <- traverse_ (notifyIfMatch event) subs
  pure unit
  where
    notifyIfMatch :: Event -> Subscription -> Effect Unit
    notifyIfMatch ev sub = case sub.filter of
      Nothing -> sub.handler ev
      Just filterType -> 
        if ev.type == filterType
          then sub.handler ev
          else pure unit

-- | Broadcast event to all subscribers
broadcast :: Event -> Effect Unit
broadcast = publish

-- | Traverse with effect (simplified)
traverse_ :: forall a. (a -> Effect Unit) -> Array a -> Effect Unit
traverse_ f arr = case Array.uncons arr of
  Nothing -> pure unit
  Just { head, tail } -> do
    f head
    traverse_ f tail

-- ════════════════════════════════════════════════════════════════════════════
-- EVENT BUILDERS
-- ════════════════════════════════════════════════════════════════════════════

-- | Session created event
sessionCreated :: String -> Event
sessionCreated sessionId =
  { type: SessionCreated
  , properties: emptyProperties { sessionID = Just sessionId }
  }

-- | Session updated event
sessionUpdated :: String -> Event
sessionUpdated sessionId =
  { type: SessionUpdated
  , properties: emptyProperties { sessionID = Just sessionId }
  }

-- | Message updated event
messageUpdated :: { sessionID :: String, messageID :: String } -> Event
messageUpdated input =
  { type: MessageUpdated
  , properties: emptyProperties 
      { sessionID = Just input.sessionID
      , messageID = Just input.messageID
      }
  }

-- | Part updated event (with optional delta for streaming)
partUpdated :: { sessionID :: String, messageID :: String, partID :: String, delta :: Maybe String } -> Event
partUpdated input =
  { type: PartUpdated
  , properties: emptyProperties
      { sessionID = Just input.sessionID
      , messageID = Just input.messageID
      , partID = Just input.partID
      , delta = input.delta
      }
  }

-- | Tool started event
toolStarted :: { sessionID :: String, toolName :: String } -> Event
toolStarted input =
  { type: ToolStarted
  , properties: emptyProperties
      { sessionID = Just input.sessionID
      , toolName = Just input.toolName
      }
  }

-- | Tool completed event
toolCompleted :: { sessionID :: String, toolName :: String } -> Event
toolCompleted input =
  { type: ToolCompleted
  , properties: emptyProperties
      { sessionID = Just input.sessionID
      , toolName = Just input.toolName
      }
  }

-- | Server connected event
serverConnected :: Event
serverConnected =
  { type: ServerConnected
  , properties: emptyProperties
  }

-- | Server heartbeat event
serverHeartbeat :: Event
serverHeartbeat =
  { type: ServerHeartbeat
  , properties: emptyProperties
  }

-- | Serialize event to SSE format
toSSE :: Event -> String
toSSE event =
  "data: " <> toJSON event <> "\n\n"
  where
    toJSON :: Event -> String
    toJSON ev = 
      "{\"type\":\"" <> show ev.type <> "\",\"properties\":{}}"
