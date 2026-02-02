-- | Event loop utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/util/eventloop.ts
module Opencode.Util.EventLoop where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Opencode.Util.NotImplemented (notImplemented)

-- | Schedule on next tick
nextTick :: Effect Unit -> Effect Unit
nextTick action = notImplemented "Util.EventLoop.nextTick"

-- | Schedule with setImmediate
setImmediate :: Effect Unit -> Effect Unit
setImmediate action = notImplemented "Util.EventLoop.setImmediate"

-- | Keep event loop alive
keepAlive :: Aff Unit
keepAlive = notImplemented "Util.EventLoop.keepAlive"
