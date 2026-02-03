-- | Bus Event types
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/bus/bus-event.ts
module Forge.Bus.BusEvent where

import Prelude

-- | Bus event types
data BusEventType
  = SessionCreated
  | SessionUpdated
  | SessionDeleted
  | MessageCreated
  | MessageUpdated
  | ToolExecuted
  | PermissionAsked
  | Error

-- | Bus event
type BusEvent =
  { type :: BusEventType
  , payload :: String  -- JSON
  , timestamp :: Number
  }
