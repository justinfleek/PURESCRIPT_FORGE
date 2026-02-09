-- | Forge Plugin SDK FFI bindings
module Bridge.FFI.Forge.Plugin where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)

-- | Opaque PluginInput type
foreign import data PluginInput :: Type

-- | Opaque Hooks type
foreign import data Hooks :: Type

-- | Opaque Event type
foreign import data Event :: Type

-- | Get event type
foreign import getEventType :: Event -> Effect String

-- | Get event payload as JSON
foreign import getEventPayload :: Event -> Effect String
