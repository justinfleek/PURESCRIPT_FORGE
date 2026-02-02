-- | Grep.purs - Content search tool
-- | TODO: Implement - mirrors opencode/src/tool/grep.ts
module Tool.Grep where

import Prelude

import Data.Maybe (Maybe)
import Effect.Aff (Aff)
import Tool (Context, Result)

-- | Grep tool parameters
type Params =
  { pattern :: String
  , path :: Maybe String
  , include :: Maybe String
  }

-- | Execute grep search
execute :: Params -> Context -> Aff Result
execute _ _ = notImplemented "Tool.Grep.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
