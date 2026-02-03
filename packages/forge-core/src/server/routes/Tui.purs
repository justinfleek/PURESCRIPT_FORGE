-- | TUI route
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/server/routes/tui.ts
module Forge.Server.Routes.Tui where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Get TUI state
get :: Aff (Either String String)
get = notImplemented "Server.Routes.Tui.get"

-- | Update TUI state
update :: String -> Aff (Either String Unit)
update state = notImplemented "Server.Routes.Tui.update"
