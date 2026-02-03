-- | Debug Skill command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/debug/skill.ts
module Forge.CLI.Cmd.Debug.Skill where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Execute debug skill command
execute :: Maybe String -> Aff (Either String Unit)
execute skillName = notImplemented "CLI.Cmd.Debug.Skill.execute"
