-- | Codex plugin
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/plugin/codex.ts
module Forge.Plugin.Codex where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Codex configuration
type CodexConfig =
  { enabled :: Boolean
  }

-- | Initialize Codex plugin
init :: CodexConfig -> Aff (Either String Unit)
init config = notImplemented "Plugin.Codex.init"
