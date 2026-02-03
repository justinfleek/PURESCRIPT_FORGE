-- | Config route
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/server/routes/config.ts
module Forge.Server.Routes.Config where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Get configuration
get :: Aff (Either String String)
get = notImplemented "Server.Routes.Config.get"

-- | Update configuration
update :: String -> Aff (Either String Unit)
update config = notImplemented "Server.Routes.Config.update"
