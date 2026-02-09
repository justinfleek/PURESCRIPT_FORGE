-- | TUI route
-- | 1:1 parity with opencode-dev/packages/opencode/src/server/routes/tui.ts
module Forge.Server.Routes.Tui where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Foreign (Foreign)

-- | Get TUI state
get :: Aff (Either String Foreign)
get = getFFI

-- | Update TUI state
update :: Foreign -> Aff (Either String Unit)
update updates = updateFFI updates

-- | Set TUI mode
setMode :: String -> Aff (Either String Unit)
setMode mode = setModeFFI mode

-- | Set TUI focus
setFocus :: String -> Aff (Either String Unit)
setFocus focus = setFocusFFI focus

foreign import getFFI :: Aff (Either String Foreign)
foreign import updateFFI :: Foreign -> Aff (Either String Unit)
foreign import setModeFFI :: String -> Aff (Either String Unit)
foreign import setFocusFFI :: String -> Aff (Either String Unit)
