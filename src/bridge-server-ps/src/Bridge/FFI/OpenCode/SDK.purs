-- | OpenCode SDK v2 FFI bindings
module Bridge.FFI.OpenCode.SDK where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe)

-- | Opaque SDK Client type
foreign import data SDKClient :: Type

-- | Opaque Event Stream type
foreign import data EventStream :: Type

-- | Opaque Event type
foreign import data Event :: Type

-- | Client config
type ClientConfig =
  { baseUrl :: String
  , directory :: String
  }

-- | Create OpenCode client
foreign import createClient :: ClientConfig -> Aff (Either String SDKClient)

-- | Connect client
foreign import connect :: SDKClient -> Aff (Either String Unit)

-- | Disconnect client
foreign import disconnect :: SDKClient -> Aff (Either String Unit)

-- | Subscribe to events
foreign import subscribeEvents :: SDKClient -> Aff (Either String EventStream)

-- | Get next event from stream
foreign import nextEvent :: EventStream -> Aff (Either String (Maybe Event))

-- | Get event type
foreign import getEventType :: Event -> Effect String

-- | Get event payload as JSON string
foreign import getEventPayload :: Event -> Effect String

-- | Close event stream
foreign import closeStream :: EventStream -> Effect Unit
