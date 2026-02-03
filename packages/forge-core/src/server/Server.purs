-- | Main Server module
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/server/server.ts
module Forge.Server.Server where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Server configuration
type ServerConfig =
  { port :: Int
  , host :: String
  , cors :: Boolean
  }

-- | Server instance
type Server =
  { config :: ServerConfig
  , isRunning :: Boolean
  }

-- | Start the server
start :: ServerConfig -> Aff (Either String Server)
start config = notImplemented "Server.Server.start"

-- | Stop the server
stop :: Server -> Aff (Either String Unit)
stop server = notImplemented "Server.Server.stop"

-- | Get the server app (for internal fetch)
app :: Unit -> Aff (Either String Unit)
app _ = notImplemented "Server.Server.app"
