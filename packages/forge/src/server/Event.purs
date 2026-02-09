-- | Server Events (SSE)
-- | Ported from: opencode-dev/packages/opencode/src/server/event.ts
module Forge.Server.Event where

import Prelude

import Data.Either (Either(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Server event type
type ServerEvent =
  { "type" :: String
  , properties :: String
  }

-- | Subscribe to server events
subscribe :: (ServerEvent -> Effect Unit) -> Aff (Either String Unit)
subscribe callback = fromEffectFnAff (subscribeFFI callback)

-- | Publish a server event
publish :: ServerEvent -> Effect Unit
publish = publishFFI

-- | Unsubscribe from server events
unsubscribe :: Effect Unit
unsubscribe = unsubscribeFFI

-- | FFI: Subscribe to events
foreign import subscribeFFI :: (ServerEvent -> Effect Unit) -> EffectFnAff (Either String Unit)

-- | FFI: Publish event
foreign import publishFFI :: ServerEvent -> Effect Unit

-- | FFI: Unsubscribe
foreign import unsubscribeFFI :: Effect Unit
