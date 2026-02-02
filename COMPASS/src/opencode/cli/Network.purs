-- | CLI Network utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/network.ts
module Opencode.CLI.Network where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

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
