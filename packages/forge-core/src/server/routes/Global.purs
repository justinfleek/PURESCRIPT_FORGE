-- | Global route
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/server/routes/global.ts
module Forge.Server.Routes.Global where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Get global state
get :: Aff (Either String String)
get = notImplemented "Server.Routes.Global.get"
