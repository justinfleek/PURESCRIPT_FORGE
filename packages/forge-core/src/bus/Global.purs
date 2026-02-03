-- | Global Bus
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/bus/global.ts
module Forge.Bus.Global where

import Prelude
import Effect (Effect)
import Forge.Bus.BusEvent (BusEvent)
import Forge.Util.NotImplemented (notImplemented)

-- | Publish to global bus
publish :: BusEvent -> Effect Unit
publish event = notImplemented "Bus.Global.publish"

-- | Subscribe to global bus
subscribe :: (BusEvent -> Effect Unit) -> Effect (Effect Unit)
subscribe handler = notImplemented "Bus.Global.subscribe"
