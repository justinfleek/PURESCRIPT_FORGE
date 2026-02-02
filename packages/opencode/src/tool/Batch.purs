-- | Batch.purs - Batch tool execution
-- | TODO: Implement - mirrors opencode/src/tool/batch.ts
module Tool.Batch where

import Prelude
import Effect.Aff (Aff)

type Params = { tools :: Array { name :: String, params :: String } }
type Result = { title :: String, output :: String }

execute :: Params -> Aff Result
execute _ = notImplemented "Tool.Batch.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
