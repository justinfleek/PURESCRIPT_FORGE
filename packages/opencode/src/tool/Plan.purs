-- | Plan.purs - Task planning tool
-- | TODO: Implement - mirrors opencode/src/tool/plan.ts
module Tool.Plan where

import Prelude
import Effect.Aff (Aff)

type Params = { plan :: String }
type Result = { title :: String, output :: String }

execute :: Params -> Aff Result
execute _ = notImplemented "Tool.Plan.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
