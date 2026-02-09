{-|
Module      : Forge.Bus.Global
Description : Global Event Bus

A publish/subscribe event bus for system-wide events.
Components can publish events and subscribe to receive them.

== Usage

@
  -- Subscribe to events
  unsubscribe <- subscribe \event ->
    case event.type of
      SessionCreated -> handleSessionCreated event
      _ -> pure unit

  -- Publish an event
  publish { type: SessionCreated, payload: sessionJson, timestamp: now }

  -- Unsubscribe when done
  unsubscribe
@
-}
module Forge.Bus.Global
  ( -- * Core Operations
    publish
  , subscribe
  , subscribeFiltered
    -- * Event History
  , getHistory
  , clearHistory
    -- * Bus Management
  , reset
  , getSubscriberCount
  ) where

import Prelude

import Data.Array as Array
import Effect (Effect)
import Forge.Bus.BusEvent (BusEvent, BusEventType)

-- ============================================================================
-- FFI
-- ============================================================================

-- | Add event to bus
foreign import publishFFI :: BusEvent -> Effect Unit

-- | Subscribe to all events, returns unsubscribe function
foreign import subscribeFFI :: (BusEvent -> Effect Unit) -> Effect (Effect Unit)

-- | Get event history
foreign import getHistoryFFI :: Effect (Array BusEvent)

-- | Clear event history
foreign import clearHistoryFFI :: Effect Unit

-- | Reset bus (clear history and subscribers)
foreign import resetFFI :: Effect Unit

-- | Get number of subscribers
foreign import getSubscriberCountFFI :: Effect Int

-- | Get current timestamp
foreign import nowFFI :: Effect Number

-- ============================================================================
-- CORE OPERATIONS
-- ============================================================================

{-| Publish an event to the global bus.

The event will be delivered to all subscribers.
-}
publish :: BusEvent -> Effect Unit
publish = publishFFI

{-| Subscribe to all events on the bus.

Returns an unsubscribe function that should be called when the
subscription is no longer needed.
-}
subscribe :: (BusEvent -> Effect Unit) -> Effect (Effect Unit)
subscribe = subscribeFFI

{-| Subscribe to events matching a filter.

Only events where the predicate returns true will be delivered.
-}
subscribeFiltered :: (BusEvent -> Boolean) -> (BusEvent -> Effect Unit) -> Effect (Effect Unit)
subscribeFiltered predicate handler =
  subscribe \event ->
    if predicate event
    then handler event
    else pure unit

-- ============================================================================
-- EVENT HISTORY
-- ============================================================================

{-| Get the event history.

Returns the most recent events (limited to prevent memory issues).
-}
getHistory :: Effect (Array BusEvent)
getHistory = getHistoryFFI

{-| Clear the event history. -}
clearHistory :: Effect Unit
clearHistory = clearHistoryFFI

-- ============================================================================
-- BUS MANAGEMENT
-- ============================================================================

{-| Reset the bus.

Clears all subscribers and history.
-}
reset :: Effect Unit
reset = resetFFI

{-| Get the number of active subscribers. -}
getSubscriberCount :: Effect Int
getSubscriberCount = getSubscriberCountFFI
