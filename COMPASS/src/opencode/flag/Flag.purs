-- | Feature Flags
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/flag/flag.ts
module Opencode.Flag.Flag where

import Prelude
import Effect (Effect)
import Opencode.Util.NotImplemented (notImplemented)

-- | Feature flag for auto-share
opencode_AUTO_SHARE :: Boolean
opencode_AUTO_SHARE = false -- TODO: Read from env

-- | Check if a feature flag is enabled
isEnabled :: String -> Effect Boolean
isEnabled flag = notImplemented "Flag.Flag.isEnabled"

-- | Get all enabled flags
getEnabled :: Effect (Array String)
getEnabled = notImplemented "Flag.Flag.getEnabled"
