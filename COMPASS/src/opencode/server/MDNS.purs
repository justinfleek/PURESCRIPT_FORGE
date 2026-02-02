-- | Server mDNS discovery
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/server/mdns.ts
module Opencode.Server.MDNS where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | mDNS service info
type MDNSService =
  { name :: String
  , host :: String
  , port :: Int
  }

-- | Advertise server via mDNS
advertise :: String -> Int -> Aff (Either String Unit)
advertise name port = notImplemented "Server.MDNS.advertise"

-- | Discover opencode servers
discover :: Aff (Either String (Array MDNSService))
discover = notImplemented "Server.MDNS.discover"

-- | Stop advertising
stopAdvertise :: Aff (Either String Unit)
stopAdvertise = notImplemented "Server.MDNS.stopAdvertise"
