-- | Write.purs - File writing tool
-- | TODO: Implement - mirrors forge/src/tool/write.ts
module Tool.Write where

import Prelude

import Effect.Aff (Aff)
import Tool (Context, Result)

-- | Write tool parameters
type Params =
  { filePath :: String
  , content :: String
  }

-- | Execute file write
execute :: Params -> Context -> Aff Result
execute _ _ = notImplemented "Tool.Write.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
