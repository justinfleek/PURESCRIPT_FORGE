-- | CLI Network utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/network.ts
module Forge.CLI.Network where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Network configuration
type NetworkConfig =
  { host :: String
  , port :: Int
  , timeout :: Int
  }

-- | Check if a server is available
checkServer :: String -> Aff (Either String Boolean)
checkServer url = notImplemented "CLI.Network.checkServer"

-- | Get available port
findAvailablePort :: Int -> Aff (Either String Int)
findAvailablePort startPort = notImplemented "CLI.Network.findAvailablePort"
