-- | OpenCode Event Handlers
module Bridge.Opencode.Events where

import Prelude
import Effect (Effect)
import Bridge.State.Store (StateStore)

-- | Handle OpenCode event
foreign import handleOpenCodeEvent :: StateStore -> String -> Effect Unit
