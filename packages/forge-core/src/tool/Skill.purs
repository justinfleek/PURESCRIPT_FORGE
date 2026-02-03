-- | Skill.purs - Skill loading tool
-- | TODO: Implement - mirrors forge/src/tool/skill.ts
module Tool.Skill where

import Prelude
import Effect.Aff (Aff)

type Params = { name :: String }
type Result = { title :: String, output :: String }

execute :: Params -> Aff Result
execute _ = notImplemented "Tool.Skill.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
