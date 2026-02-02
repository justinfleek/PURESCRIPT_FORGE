-- | Context utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/util/context.ts
module Opencode.Util.Context where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Context storage (similar to AsyncLocalStorage in Node)
-- | In PureScript, we use Reader monad or similar patterns

-- | Get a value from context
get :: forall a. String -> Effect (Maybe a)
get key = notImplemented "Util.Context.get"

-- | Set a value in context
set :: forall a. String -> a -> Effect Unit
set key value = notImplemented "Util.Context.set"

-- | Run with context
runWith :: forall a b. String -> a -> Effect b -> Effect b
runWith key value action = notImplemented "Util.Context.runWith"
