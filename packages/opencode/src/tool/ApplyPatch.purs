-- | ApplyPatch.purs - Apply unified diff patches
-- | TODO: Implement - mirrors opencode/src/tool/apply_patch.ts
module Tool.ApplyPatch where

import Prelude
import Effect.Aff (Aff)

type Params = { patch :: String }
type Result = { title :: String, output :: String }

execute :: Params -> Aff Result
execute _ = notImplemented "Tool.ApplyPatch.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
