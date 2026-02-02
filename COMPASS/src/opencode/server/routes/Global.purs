-- | Global route
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/server/routes/global.ts
module Opencode.Server.Routes.Global where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Get global state
get :: Aff (Either String String)
get = notImplemented "Server.Routes.Global.get"
