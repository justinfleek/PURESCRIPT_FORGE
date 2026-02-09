-- | Server mDNS discovery
-- | Ported from: opencode-dev/packages/opencode/src/server/mdns.ts
module Forge.Server.MDNS where

import Prelude

import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | mDNS service record
type MDNSService =
  { name :: String
  , host :: String
  , port :: Int
  }

-- | Advertise a service via mDNS
advertise :: String -> Int -> Aff (Either String Unit)
advertise name port = fromEffectFnAff (advertiseFFI name port)

-- | Discover services via mDNS
discover :: Aff (Either String (Array MDNSService))
discover = fromEffectFnAff discoverFFI

-- | Stop advertising
stopAdvertise :: Aff (Either String Unit)
stopAdvertise = fromEffectFnAff stopAdvertiseFFI

-- | FFI: Advertise service
foreign import advertiseFFI :: String -> Int -> EffectFnAff (Either String Unit)

-- | FFI: Discover services
foreign import discoverFFI :: EffectFnAff (Either String (Array MDNSService))

-- | FFI: Stop advertising
foreign import stopAdvertiseFFI :: EffectFnAff (Either String Unit)
