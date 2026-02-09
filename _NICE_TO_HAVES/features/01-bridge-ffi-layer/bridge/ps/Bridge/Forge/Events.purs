-- | Forge Event Handlers
-- | PureScript implementation
module Bridge.Forge.Events where

import Prelude
import Effect (Effect)
import Bridge.State.Store (StateStore, updateSessionPartial, updateMetricsPartial)

-- | Handle Forge event
foreign import handleForgeEvent :: StateStore -> String -> Effect Unit
