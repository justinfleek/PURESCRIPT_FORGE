-- | Experimental routes
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/server/routes/experimental.ts
module Forge.Server.Routes.Experimental where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Experimental feature handler
experimental :: String -> Aff (Either String String)
experimental feature = notImplemented "Server.Routes.Experimental.experimental"
