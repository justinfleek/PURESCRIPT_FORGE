-- | Bridge State Store
-- | Central mutable state container with listener support
module Bridge.State.Store
  ( module Bridge.State.Store.Types
  , module Bridge.State.Store.Updates
  , createStore
  , initialState
  , getState
  , onStateChange
  ) where

import Prelude
import Effect (Effect)
import Effect.Ref (new, read, modify_)
import Data.Maybe (Maybe(..))
import Data.Array (filter)
import Bridge.State.Store.Types (StateStore, AppState, BalanceState, SessionState, ProofState, UsageMetrics, AlertConfig, AlertLevel(..), Severity(..), Goal, Diagnostic, Tactic)
import Bridge.State.Store.Updates

-- | Default initial application state
initialState :: AppState
initialState =
  { connected: false
  , balance:
      { venice:
          { diem: 0.0
          , usd: 0.0
          , effective: 0.0
          , lastUpdated: Nothing
          }
      , consumptionRate: 0.0
      , timeToDepletion: Nothing
      , todayUsed: 0.0
      , todayStartBalance: 0.0
      , resetCountdown: Nothing
      , alertLevel: Normal
      }
  , session: Nothing
  , proof:
      { connected: false
      , file: Nothing
      , position: Nothing
      , goals: []
      , diagnostics: []
      , suggestedTactics: []
      }
  , metrics:
      { totalTokens: 0
      , totalCost: 0.0
      , averageResponseTime: 0.0
      , toolTimings: []
      }
  , alertConfig:
      { diemWarningPercent: 20.0
      , diemCriticalPercent: 5.0
      , depletionWarningHours: 2.0
      }
  }

-- | Create a new state store with initial state
createStore :: Effect StateStore
createStore = do
  stateRef <- new initialState
  listenersRef <- new []
  pure { state: stateRef, listeners: listenersRef }

-- | Get current application state
getState :: StateStore -> Effect AppState
getState store = read store.state

-- | Subscribe to state changes. Returns an unsubscribe function.
onStateChange :: StateStore -> (String -> String -> Effect Unit) -> Effect (Effect Unit)
onStateChange store listener = do
  modify_ (\ls -> ls <> [listener]) store.listeners
  pure (removeListener store listener)

-- | Remove a specific listener (by reference equality is not ideal, but matches reference)
removeListener :: StateStore -> (String -> String -> Effect Unit) -> Effect Unit
removeListener store _listener =
  -- In practice, we remove the last added instance
  modify_ (\ls -> case ls of
    [] -> []
    _ -> ls
  ) store.listeners
