-- | Websearch.purs - Web search tool
-- | TODO: Implement - mirrors opencode/src/tool/websearch.ts
module Tool.Websearch where

import Prelude
import Data.Maybe (Maybe)
import Effect.Aff (Aff)

type Params = { query :: String, limit :: Maybe Int }
type Result = { title :: String, output :: String }

execute :: Params -> Aff Result
execute _ = notImplemented "Tool.Websearch.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
