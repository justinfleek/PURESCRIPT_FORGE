-- | Multiedit.purs - Multiple file edits tool
-- | TODO: Implement - mirrors opencode/src/tool/multiedit.ts
module Tool.Multiedit where

import Prelude
import Effect.Aff (Aff)

type Edit = { filePath :: String, oldString :: String, newString :: String }
type Params = { edits :: Array Edit }
type Result = { title :: String, output :: String }

execute :: Params -> Aff Result
execute _ = notImplemented "Tool.Multiedit.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
