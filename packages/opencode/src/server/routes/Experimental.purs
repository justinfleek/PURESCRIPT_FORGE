-- | Experimental routes
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/server/routes/experimental.ts
module Opencode.Server.Routes.Experimental where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Experimental feature handler
experimental :: String -> Aff (Either String String)
experimental feature = notImplemented "Server.Routes.Experimental.experimental"
