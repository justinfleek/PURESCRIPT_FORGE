-- | Debug command index
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/debug/index.ts
module Opencode.CLI.Cmd.Debug.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Debug command types
data DebugCommand
  = DebugAgent
  | DebugConfig
  | DebugFile
  | DebugLsp
  | DebugRipgrep
  | DebugScrap
  | DebugSkill
  | DebugSnapshot

-- | Execute debug command
execute :: DebugCommand -> Aff (Either String Unit)
execute cmd = notImplemented "CLI.Cmd.Debug.Index.execute"
