-- | Bus Event types
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/bus/bus-event.ts
module Opencode.Bus.BusEvent where

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
