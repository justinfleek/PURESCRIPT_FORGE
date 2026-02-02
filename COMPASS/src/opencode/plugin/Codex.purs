-- | Codex plugin
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/plugin/codex.ts
module Opencode.Plugin.Codex where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Codex configuration
type CodexConfig =
  { enabled :: Boolean
  }

-- | Initialize Codex plugin
init :: CodexConfig -> Aff (Either String Unit)
init config = notImplemented "Plugin.Codex.init"
