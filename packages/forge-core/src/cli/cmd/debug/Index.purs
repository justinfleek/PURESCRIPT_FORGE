-- | Debug command index
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/debug/index.ts
module Forge.CLI.Cmd.Debug.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

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
