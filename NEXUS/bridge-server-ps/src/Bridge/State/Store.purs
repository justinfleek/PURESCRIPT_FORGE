-- | State Store - Simple state management for Bridge Server
module Bridge.State.Store where

import Prelude
import Effect (Effect)
import Effect.Ref (Ref, new, read, write)

-- | Simple state store (minimal for NEXUS)
type StateStore =
  { ref :: Ref Unit
  }

-- | Create state store
createStore :: Effect StateStore
createStore = do
  ref <- new unit
  pure { ref }

-- | Set connected state
setConnected :: StateStore -> Boolean -> Effect Unit
setConnected store connected = do
  read store.ref
  pure unit
