-- | Ls.purs - Directory listing tool
-- | TODO: Implement - mirrors forge/src/tool/ls.ts
module Tool.Ls where

import Prelude
import Data.Maybe (Maybe)
import Effect.Aff (Aff)

type Params = { path :: Maybe String }
type Result = { title :: String, output :: String }

execute :: Params -> Aff Result
execute _ = notImplemented "Tool.Ls.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
