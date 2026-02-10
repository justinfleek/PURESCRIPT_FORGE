-- | OpenCode SDK FFI bindings
module Bridge.FFI.OpenCode.SDK where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Either (Either)
import Data.Maybe (Maybe)

-- | Opaque OpenCode client type
foreign import data OpenCodeClient :: Type

-- | Opaque event stream type
foreign import data EventStream :: Type

-- | Opaque event type
foreign import data OpenCodeEvent :: Type

-- | FFI implementations
foreign import createClientImpl :: String -> String -> EffectFnAff (Either String OpenCodeClient)
foreign import connectImpl :: OpenCodeClient -> EffectFnAff (Either String Unit)
foreign import disconnectImpl :: OpenCodeClient -> EffectFnAff Unit
foreign import subscribeEventsImpl :: OpenCodeClient -> EffectFnAff (Either String EventStream)
foreign import nextEventImpl :: EventStream -> EffectFnAff (Maybe OpenCodeEvent)
foreign import getEventTypeImpl :: OpenCodeEvent -> Effect String
foreign import getEventPayloadImpl :: OpenCodeEvent -> Effect String
foreign import closeStreamImpl :: EventStream -> EffectFnAff Unit

-- | Create OpenCode SDK client
createClient :: String -> String -> Aff (Either String OpenCodeClient)
createClient apiUrl directory = fromEffectFnAff $ createClientImpl apiUrl directory

-- | Connect to OpenCode
connect :: OpenCodeClient -> Aff (Either String Unit)
connect client = fromEffectFnAff $ connectImpl client

-- | Disconnect from OpenCode
disconnect :: OpenCodeClient -> Aff Unit
disconnect client = fromEffectFnAff $ disconnectImpl client

-- | Subscribe to event stream
subscribeEvents :: OpenCodeClient -> Aff (Either String EventStream)
subscribeEvents client = fromEffectFnAff $ subscribeEventsImpl client

-- | Get next event from stream
nextEvent :: EventStream -> Aff (Maybe OpenCodeEvent)
nextEvent stream = fromEffectFnAff $ nextEventImpl stream

-- | Get event type
getEventType :: OpenCodeEvent -> Effect String
getEventType = getEventTypeImpl

-- | Get event payload as JSON string
getEventPayload :: OpenCodeEvent -> Effect String
getEventPayload = getEventPayloadImpl

-- | Close event stream
closeStream :: EventStream -> Aff Unit
closeStream stream = fromEffectFnAff $ closeStreamImpl stream
