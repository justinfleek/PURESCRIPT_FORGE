-- | Debug Skill command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/debug/skill.ts
module Opencode.CLI.Cmd.Debug.Skill where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Execute debug skill command
execute :: Maybe String -> Aff (Either String Unit)
execute skillName = notImplemented "CLI.Cmd.Debug.Skill.execute"
