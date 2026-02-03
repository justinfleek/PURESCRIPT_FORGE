-- | Server Events (SSE)
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/server/event.ts
module Forge.Server.Event where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Event type
type ServerEvent =
  { type :: String
  , properties :: String  -- JSON string
  }

-- | Subscribe to server events
subscribe :: (ServerEvent -> Effect Unit) -> Aff (Either String Unit)
subscribe handler = notImplemented "Server.Event.subscribe"

-- | Publish an event
publish :: ServerEvent -> Effect Unit
publish event = notImplemented "Server.Event.publish"
