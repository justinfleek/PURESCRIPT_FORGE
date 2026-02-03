-- | Glob.purs - File pattern matching tool
-- | TODO: Implement - mirrors forge/src/tool/glob.ts
module Tool.Glob where

import Prelude

import Data.Maybe (Maybe)
import Effect.Aff (Aff)
import Tool (Context, Result)

-- | Glob tool parameters
type Params =
  { pattern :: String
  , path :: Maybe String
  }

-- | Execute glob search
execute :: Params -> Context -> Aff Result
execute _ _ = notImplemented "Tool.Glob.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
