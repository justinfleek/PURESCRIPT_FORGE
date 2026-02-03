-- | IIFE (Immediately Invoked Function Expression) utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/util/iife.ts
-- | Note: In PureScript, this pattern is not as necessary due to pure functional nature
module Forge.Util.IIFE where

import Prelude

-- | Execute a function immediately and return its result
-- | In PureScript, this is just function application
iife :: forall a. (Unit -> a) -> a
iife f = f unit
