-- | Codesearch.purs - Code search tool
-- | TODO: Implement - mirrors opencode/src/tool/codesearch.ts
module Tool.Codesearch where

import Prelude
import Data.Maybe (Maybe)
import Effect.Aff (Aff)

type Params = { query :: String, path :: Maybe String }
type Result = { title :: String, output :: String }

execute :: Params -> Aff Result
execute _ = notImplemented "Tool.Codesearch.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
