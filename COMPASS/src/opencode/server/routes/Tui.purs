-- | TUI route
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/server/routes/tui.ts
module Opencode.Server.Routes.Tui where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Get TUI state
get :: Aff (Either String String)
get = notImplemented "Server.Routes.Tui.get"

-- | Update TUI state
update :: String -> Aff (Either String Unit)
update state = notImplemented "Server.Routes.Tui.update"
