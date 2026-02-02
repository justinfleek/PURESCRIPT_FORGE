-- | NEXUS WebSocket Handlers
module Bridge.NEXUS.Handlers where

import Prelude
import Effect.Aff (Aff)
import Data.Argonaut (Json)

-- | NEXUS Handler Context
type NexusContext =
  { sessionId :: String
  }

-- | Handle NEXUS message
handleNexusMessage :: NexusContext -> Json -> Aff Unit
handleNexusMessage _ _ = pure unit

-- | Handle NEXUS state sync
handleStateSync :: NexusContext -> Aff Unit
handleStateSync _ = pure unit

-- | Handle NEXUS agent event
handleAgentEvent :: NexusContext -> Json -> Aff Unit
handleAgentEvent _ _ = pure unit
