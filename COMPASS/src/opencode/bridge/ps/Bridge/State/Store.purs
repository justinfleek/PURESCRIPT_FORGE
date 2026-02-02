{-|
Module      : Bridge.State.Store
Description : Single Source of Truth for Bridge Server Application State
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= State Store

Provides centralized state management for the Bridge Server, maintaining
application state (balance, session, proof, metrics) in a mutable reference
with change notification support.

== Module Structure

The Store module is split into sub-modules for maintainability:

* "Bridge.State.Store.Types" - Type definitions (AppState, BalanceState, etc.)
* "Bridge.State.Store.Updates" - Update functions (updateBalance, etc.)

== Mathematical Foundation

- State Invariant: The state store always contains a valid AppState
- Update Invariant: All update functions preserve state validity
- Listener Invariant: Listeners are notified synchronously after state updates

== Usage Example

@
  import Bridge.State.Store as Store

  -- Create state store
  store <- Store.createStore

  -- Get current state
  currentState <- Store.getState store

  -- Update balance
  Store.updateBalance store newBalance

  -- Subscribe to state changes
  unsubscribe <- Store.onStateChange store \\path value -> do
    log $ "State changed: " <> path <> " = " <> value

  -- Later: unsubscribe
  unsubscribe
@

Based on spec 41-STATE-MANAGEMENT.md
-}
module Bridge.State.Store
  ( -- * Re-exports
    module Bridge.State.Store.Types
  , module Bridge.State.Store.Updates
    -- * Store Creation
  , createStore
  , initialState
    -- * State Access
  , getState
    -- * Subscriptions
  , onStateChange
  ) where

import Prelude

import Effect (Effect)
import Effect.Ref (Ref, new, read, modify)
import Data.DateTime (DateTime)
import Data.Maybe (Maybe(..))
import Data.Array (Array)
import Data.Array as Array

import Bridge.State.Store.Types
import Bridge.State.Store.Updates

-- ============================================================================
-- INITIAL STATE
-- ============================================================================

{-| Create initial state - Default application state.

Default Values:
- connected: false (not connected until WebSocket establishes)
- balance: All zeros, Normal alert level
- session: Nothing (no active session)
- proof: Not connected, empty arrays
- metrics: All zeros
- alertConfig: Standard thresholds (20% warning, 5% critical, 2 hours)
-}
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
      { diemWarningPercent: 0.20
      , diemCriticalPercent: 0.05
      , depletionWarningHours: 2.0
      }
  }

-- ============================================================================
-- STORE CREATION
-- ============================================================================

{-| Create state store - Initialize mutable state container. -}
createStore :: Effect StateStore
createStore = do
  state <- new initialState
  listeners <- new []
  pure { state, listeners }

-- ============================================================================
-- STATE ACCESS
-- ============================================================================

{-| Get current state - Read current application state. -}
getState :: StateStore -> Effect AppState
getState store = read store.state

-- ============================================================================
-- SUBSCRIPTIONS
-- ============================================================================

{-| Subscribe to state changes - Register change listener.

Returns an unsubscribe function to remove the listener.

Listener Parameters:
- path: State path that changed (e.g., "balance", "session", "proof")
- value: Change description (e.g., "updated", "cleared", "connected")
-}
onStateChange :: StateStore -> (String -> String -> Effect Unit) -> Effect (Effect Unit)
onStateChange store listener = do
  modify (\listeners -> listeners <> [listener]) store.listeners
  pure do
    modify (\listeners -> Array.filter (\l -> l /= listener) listeners) store.listeners
