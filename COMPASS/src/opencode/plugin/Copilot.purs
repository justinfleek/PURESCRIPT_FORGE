-- | Copilot plugin
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/plugin/copilot.ts
module Opencode.Plugin.Copilot where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Copilot configuration
type CopilotConfig =
  { enabled :: Boolean
  }

-- | Initialize Copilot plugin
init :: CopilotConfig -> Aff (Either String Unit)
init config = notImplemented "Plugin.Copilot.init"
