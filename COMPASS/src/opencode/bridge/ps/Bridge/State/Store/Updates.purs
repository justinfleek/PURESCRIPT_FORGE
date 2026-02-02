{-|
Module      : Bridge.State.Store.Updates
Description : State update functions
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= State Updates

Functions for updating Bridge Server application state.
All updates notify registered listeners.

== Update Strategies

- Partial updates: Merge provided fields with existing state
- Full updates: Replace entire state slice

== Listener Notification

All update functions call notifyListeners with:
- path: State path that changed (e.g., "balance", "session")
- value: Change description (e.g., "updated", "cleared")
-}
module Bridge.State.Store.Updates
  ( -- * Balance Updates
    updateBalance
  , updateBalancePartial
    -- * Session Updates
  , updateSession
  , updateSessionPartial
  , clearSession
    -- * Proof Updates
  , updateProof
  , updateProofPartial
    -- * Metrics Updates
  , updateMetrics
  , updateMetricsPartial
    -- * Other Updates
  , setConnected
  , updateAlertConfig
    -- * Internal
  , notifyListeners
  ) where

import Prelude

import Effect (Effect)
import Effect.Ref (read, write, modify)
import Data.DateTime (DateTime)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Array (Array)
import Data.Foldable (traverse_)

import Bridge.State.Store.Types

-- ============================================================================
-- BALANCE UPDATES
-- ============================================================================

{-| Update balance (full) - Replace entire balance state. -}
updateBalance :: StateStore -> BalanceState -> Effect Unit
updateBalance store newBalance = do
  current <- read store.state
  write store.state (current { balance = newBalance })
  notifyListeners store "balance" "updated"

{-| Update balance (partial) - Merge partial balance updates. -}
updateBalancePartial :: StateStore -> BalancePartial -> Effect Unit
updateBalancePartial store partial = do
  current <- read store.state
  let balance = current.balance
  let newBalance = balance
        { venice = case partial.venice of
            Just v -> balance.venice
              { diem = fromMaybe balance.venice.diem v.diem
              , usd = fromMaybe balance.venice.usd v.usd
              , effective = fromMaybe balance.venice.effective v.effective
              , lastUpdated = fromMaybe balance.venice.lastUpdated v.lastUpdated
              }
            Nothing -> balance.venice
        , consumptionRate = fromMaybe balance.consumptionRate partial.consumptionRate
        , timeToDepletion = fromMaybe balance.timeToDepletion (partial.timeToDepletion >>= identity)
        , todayUsed = fromMaybe balance.todayUsed partial.todayUsed
        , resetCountdown = fromMaybe balance.resetCountdown (partial.resetCountdown >>= identity)
        , alertLevel = fromMaybe balance.alertLevel partial.alertLevel
        }
  write store.state (current { balance = newBalance })
  notifyListeners store "balance" "updated"

type BalancePartial =
  { venice :: Maybe { diem :: Maybe Number, usd :: Maybe Number, effective :: Maybe Number, lastUpdated :: Maybe DateTime }
  , consumptionRate :: Maybe Number
  , timeToDepletion :: Maybe (Maybe Number)
  , todayUsed :: Maybe Number
  , resetCountdown :: Maybe (Maybe Number)
  , alertLevel :: Maybe AlertLevel
  }

-- ============================================================================
-- SESSION UPDATES
-- ============================================================================

{-| Update session (full) - Replace entire session state. -}
updateSession :: StateStore -> SessionState -> Effect Unit
updateSession store newSession = do
  current <- read store.state
  write store.state (current { session = Just newSession })
  notifyListeners store "session" "updated"

{-| Update session (partial) - Merge partial session updates. -}
updateSessionPartial :: StateStore -> SessionPartial -> Effect Unit
updateSessionPartial store partial = do
  current <- read store.state
  case current.session of
    Just session -> do
      let newSession = session
            { id = fromMaybe session.id partial.id
            , promptTokens = fromMaybe session.promptTokens partial.promptTokens
            , completionTokens = fromMaybe session.completionTokens partial.completionTokens
            , totalTokens = fromMaybe session.totalTokens partial.totalTokens
            , cost = fromMaybe session.cost partial.cost
            , model = fromMaybe session.model partial.model
            , provider = fromMaybe session.provider partial.provider
            , messageCount = fromMaybe session.messageCount partial.messageCount
            , updatedAt = fromMaybe session.updatedAt partial.updatedAt
            }
      write store.state (current { session = Just newSession })
      notifyListeners store "session" "updated"
    Nothing -> pure unit

{-| Clear session - Remove active session. -}
clearSession :: StateStore -> Effect Unit
clearSession store = do
  current <- read store.state
  write store.state (current { session = Nothing })
  notifyListeners store "session" "cleared"

type SessionPartial =
  { id :: Maybe String
  , promptTokens :: Maybe Int
  , completionTokens :: Maybe Int
  , totalTokens :: Maybe Int
  , cost :: Maybe Number
  , model :: Maybe String
  , provider :: Maybe String
  , messageCount :: Maybe Int
  , updatedAt :: Maybe DateTime
  }

-- ============================================================================
-- PROOF UPDATES
-- ============================================================================

{-| Update proof state (full) - Replace entire proof state. -}
updateProof :: StateStore -> ProofState -> Effect Unit
updateProof store newProof = do
  current <- read store.state
  write store.state (current { proof = newProof })
  notifyListeners store "proof" "updated"

{-| Update proof state (partial) - Merge partial proof updates. -}
updateProofPartial :: StateStore -> ProofPartial -> Effect Unit
updateProofPartial store partial = do
  current <- read store.state
  let proof = current.proof
  let newProof = proof
        { connected = fromMaybe proof.connected partial.connected
        , file = fromMaybe proof.file (partial.file >>= identity)
        , position = fromMaybe proof.position (partial.position >>= identity)
        , goals = fromMaybe proof.goals partial.goals
        , diagnostics = fromMaybe proof.diagnostics partial.diagnostics
        , suggestedTactics = fromMaybe proof.suggestedTactics partial.suggestedTactics
        }
  write store.state (current { proof = newProof })
  notifyListeners store "proof" "updated"

type ProofPartial =
  { connected :: Maybe Boolean
  , file :: Maybe (Maybe String)
  , position :: Maybe (Maybe { line :: Int, column :: Int })
  , goals :: Maybe (Array Goal)
  , diagnostics :: Maybe (Array Diagnostic)
  , suggestedTactics :: Maybe (Array Tactic)
  }

-- ============================================================================
-- METRICS UPDATES
-- ============================================================================

{-| Update metrics (full) - Replace entire metrics state. -}
updateMetrics :: StateStore -> UsageMetrics -> Effect Unit
updateMetrics store newMetrics = do
  current <- read store.state
  write store.state (current { metrics = newMetrics })
  notifyListeners store "metrics" "updated"

{-| Update metrics (partial) - Merge partial metrics updates. -}
updateMetricsPartial :: StateStore -> MetricsPartial -> Effect Unit
updateMetricsPartial store partial = do
  current <- read store.state
  let metrics = current.metrics
  let newMetrics = metrics
        { totalTokens = fromMaybe metrics.totalTokens partial.totalTokens
        , totalCost = fromMaybe metrics.totalCost partial.totalCost
        , averageResponseTime = fromMaybe metrics.averageResponseTime partial.averageResponseTime
        , toolTimings = fromMaybe metrics.toolTimings partial.toolTimings
        }
  write store.state (current { metrics = newMetrics })
  notifyListeners store "metrics" "updated"

type MetricsPartial =
  { totalTokens :: Maybe Int
  , totalCost :: Maybe Number
  , averageResponseTime :: Maybe Number
  , toolTimings :: Maybe (Array { tool :: String, duration :: Number })
  }

-- ============================================================================
-- OTHER UPDATES
-- ============================================================================

{-| Set connected state - Update WebSocket connection status. -}
setConnected :: StateStore -> Boolean -> Effect Unit
setConnected store connected = do
  current <- read store.state
  write store.state (current { connected = connected })
  notifyListeners store "connected" (if connected then "connected" else "disconnected")

{-| Update alert configuration - Replace alert thresholds. -}
updateAlertConfig :: StateStore -> AlertConfig -> Effect Unit
updateAlertConfig store newConfig = do
  current <- read store.state
  write store.state (current { alertConfig = newConfig })
  notifyListeners store "alertConfig" "updated"

-- ============================================================================
-- LISTENER NOTIFICATION
-- ============================================================================

{-| Notify all listeners - Internal function to trigger change notifications. -}
notifyListeners :: StateStore -> String -> String -> Effect Unit
notifyListeners store path value = do
  listeners <- read store.listeners
  traverse_ (\listener -> listener path value) listeners
