-- | IIFE (Immediately Invoked Function Expression) utilities
-- | Note: In PureScript, this pattern is not as necessary due to pure functional nature
module Opencode.Util.IIFE where

import Prelude

-- | Execute a function immediately and return its result
-- | In PureScript, this is just function application
iife :: forall a. (Unit -> a) -> a
iife f = f unit
