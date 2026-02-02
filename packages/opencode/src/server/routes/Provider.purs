-- | Provider route
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/server/routes/provider.ts
module Opencode.Server.Routes.Provider where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | List providers
list :: Aff (Either String (Array String))
list = notImplemented "Server.Routes.Provider.list"

-- | Get provider info
get :: String -> Aff (Either String String)
get provider = notImplemented "Server.Routes.Provider.get"
