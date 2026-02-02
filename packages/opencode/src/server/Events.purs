-- | OpenCode Event Handlers
-- | PureScript implementation
module Bridge.Opencode.Events where

import Prelude
import Effect (Effect)
import Bridge.State.Store (StateStore, updateSessionPartial, updateMetricsPartial)

-- | Handle OpenCode event
foreign import handleOpenCodeEvent :: StateStore -> String -> Effect Unit
