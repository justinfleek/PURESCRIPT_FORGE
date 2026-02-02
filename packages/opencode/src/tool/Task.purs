-- | Task.purs - Sub-agent task tool
-- | TODO: Implement - mirrors opencode/src/tool/task.ts
module Tool.Task where

import Prelude
import Data.Maybe (Maybe)
import Effect.Aff (Aff)

type Params = 
  { description :: String
  , prompt :: String
  , subagentType :: String
  , sessionId :: Maybe String
  , command :: Maybe String
  }
type Result = { title :: String, output :: String }

execute :: Params -> Aff Result
execute _ = notImplemented "Tool.Task.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
