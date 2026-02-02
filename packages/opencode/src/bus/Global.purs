-- | Global Bus
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/bus/global.ts
module Opencode.Bus.Global where

import Prelude
import Effect (Effect)
import Opencode.Bus.BusEvent (BusEvent)
import Opencode.Util.NotImplemented (notImplemented)

-- | Publish to global bus
publish :: BusEvent -> Effect Unit
publish event = notImplemented "Bus.Global.publish"

-- | Subscribe to global bus
subscribe :: (BusEvent -> Effect Unit) -> Effect (Effect Unit)
subscribe handler = notImplemented "Bus.Global.subscribe"
