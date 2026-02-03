-- | Invalid.purs - Invalid tool handling
-- | TODO: Implement - mirrors forge/src/tool/invalid.ts
module Tool.Invalid where

import Prelude
import Effect.Aff (Aff)

type Params = { name :: String, reason :: String }
type Result = { title :: String, output :: String }

execute :: Params -> Aff Result
execute _ = notImplemented "Tool.Invalid.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
