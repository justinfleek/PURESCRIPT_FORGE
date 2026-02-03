-- | Feature Flags
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/flag/flag.ts
module Forge.Flag.Flag where

import Prelude
import Effect (Effect)
import Forge.Util.NotImplemented (notImplemented)

-- | Feature flag for auto-share
forge_AUTO_SHARE :: Boolean
forge_AUTO_SHARE = false -- TODO: Read from env

-- | Check if a feature flag is enabled
isEnabled :: String -> Effect Boolean
isEnabled flag = notImplemented "Flag.Flag.isEnabled"

-- | Get all enabled flags
getEnabled :: Effect (Array String)
getEnabled = notImplemented "Flag.Flag.getEnabled"
