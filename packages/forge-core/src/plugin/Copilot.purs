-- | Copilot plugin
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/plugin/copilot.ts
module Forge.Plugin.Copilot where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Copilot configuration
type CopilotConfig =
  { enabled :: Boolean
  }

-- | Initialize Copilot plugin
init :: CopilotConfig -> Aff (Either String Unit)
init config = notImplemented "Plugin.Copilot.init"
