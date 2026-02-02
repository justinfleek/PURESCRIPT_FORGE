-- | Provider Transform utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/provider/transform.ts
module Opencode.Provider.Transform where

import Prelude
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Transform input for a specific provider
transformInput :: forall a. String -> a -> a
transformInput provider input = notImplemented "Provider.Transform.transformInput"

-- | Transform output from a specific provider
transformOutput :: forall a. String -> a -> a
transformOutput provider output = notImplemented "Provider.Transform.transformOutput"
