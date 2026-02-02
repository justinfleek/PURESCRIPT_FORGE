-- | Bridge Client WebSocket FFI
-- | For plugin to communicate with Bridge Server
module Bridge.FFI.WebSocket.Client where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either)

-- | Opaque Bridge Client type
foreign import data BridgeClient :: Type

-- | Create bridge client
foreign import createClient :: String -> Effect BridgeClient

-- | Connect to bridge server
foreign import connect :: BridgeClient -> Aff (Either String Unit)

-- | Send event
foreign import sendEvent :: BridgeClient -> String -> Aff (Either String Unit)

-- | Send message
foreign import sendMessage :: BridgeClient -> String -> Aff (Either String Unit)

-- | Send tool execution
foreign import sendToolExecution :: BridgeClient -> String -> Aff (Either String Unit)

-- | Send config
foreign import sendConfig :: BridgeClient -> String -> Aff (Either String Unit)
