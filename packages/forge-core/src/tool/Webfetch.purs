-- | Webfetch.purs - URL fetching tool
-- | TODO: Implement - mirrors forge/src/tool/webfetch.ts
module Tool.Webfetch where

import Prelude
import Data.Maybe (Maybe)
import Effect.Aff (Aff)

type Params = { url :: String, format :: Maybe String, timeout :: Maybe Int }
type Result = { title :: String, output :: String }

execute :: Params -> Aff Result
execute _ = notImplemented "Tool.Webfetch.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
