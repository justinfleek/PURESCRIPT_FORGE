-- | Event loop utilities
module Opencode.Util.EventLoop where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)

-- | Schedule on next tick
nextTick :: Effect Unit -> Effect Unit
nextTick action = processNextTick action
  where
    foreign import processNextTick :: Effect Unit -> Effect Unit

-- | Schedule with setImmediate
setImmediate :: Effect Unit -> Effect Unit
setImmediate action = scheduleImmediate action
  where
    foreign import scheduleImmediate :: Effect Unit -> Effect Unit

-- | Keep event loop alive
keepAlive :: Aff Unit
keepAlive = liftEffect keepAliveLoop
  where
    foreign import keepAliveLoop :: Effect Unit
