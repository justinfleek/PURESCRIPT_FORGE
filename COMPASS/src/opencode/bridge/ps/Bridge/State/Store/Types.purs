{-|
Module      : Bridge.State.Store.Types
Description : Type definitions for Bridge Server state
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= State Types

Core type definitions for the Bridge Server application state.
Includes balance, session, proof, metrics, and alert configuration.

== State Invariants

- All numeric values >= 0 (no negative balances, tokens, or costs)
- totalTokens = promptTokens + completionTokens
- updatedAt >= startedAt for sessions
- diemCriticalPercent < diemWarningPercent for alerts
-}
module Bridge.State.Store.Types
  ( -- * Balance Types
    BalanceState(..)
  , AlertLevel(..)
  , AlertConfig(..)
    -- * Session Types
  , SessionState(..)
    -- * Proof Types
  , ProofState(..)
  , Goal(..)
  , Diagnostic(..)
  , Severity(..)
  , Tactic(..)
    -- * Metrics Types
  , UsageMetrics(..)
    -- * Application State
  , AppState(..)
    -- * Store Types
  , StateStore(..)
  ) where

import Prelude

import Effect (Effect)
import Effect.Ref (Ref)
import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Data.Array (Array)

-- ============================================================================
-- BALANCE TYPES
-- ============================================================================

{-| Balance state - Token balance and consumption tracking.

Invariants:
- consumptionRate >= 0.0
- todayUsed >= 0.0
- alertLevel is calculated from balance thresholds
-}
type BalanceState =
  { venice ::
      { diem :: Number
      , usd :: Number
      , effective :: Number
      , lastUpdated :: Maybe DateTime
      }
  , consumptionRate :: Number
  , timeToDepletion :: Maybe Number
  , todayUsed :: Number
  , todayStartBalance :: Number
  , resetCountdown :: Maybe Number
  , alertLevel :: AlertLevel
  }

{-| Alert level - Balance depletion warning levels. -}
data AlertLevel = Normal | Warning | Critical

derive instance eqAlertLevel :: Eq AlertLevel

{-| Alert configuration - Balance alert thresholds.

Invariants:
- 0.0 <= diemWarningPercent <= 1.0
- 0.0 <= diemCriticalPercent <= 1.0
- diemCriticalPercent < diemWarningPercent
- depletionWarningHours >= 0.0
-}
type AlertConfig =
  { diemWarningPercent :: Number
  , diemCriticalPercent :: Number
  , depletionWarningHours :: Number
  }

-- ============================================================================
-- SESSION TYPES
-- ============================================================================

{-| Session state - Active chat session tracking.

Invariants:
- totalTokens = promptTokens + completionTokens
- promptTokens >= 0 and completionTokens >= 0
- cost >= 0.0
- messageCount >= 0
- updatedAt >= startedAt
-}
type SessionState =
  { id :: String
  , promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cost :: Number
  , model :: String
  , provider :: String
  , messageCount :: Int
  , startedAt :: DateTime
  , updatedAt :: DateTime
  }

-- ============================================================================
-- PROOF TYPES
-- ============================================================================

{-| Proof state - Lean4 LSP connection and proof status.

Invariants:
- position is Nothing if file is Nothing
-}
type ProofState =
  { connected :: Boolean
  , file :: Maybe String
  , position :: Maybe { line :: Int, column :: Int }
  , goals :: Array Goal
  , diagnostics :: Array Diagnostic
  , suggestedTactics :: Array Tactic
  }

{-| Goal - Lean4 proof goal. -}
type Goal =
  { type_ :: String
  , context :: Array { name :: String, type_ :: String }
  }

{-| Diagnostic - Lean4 LSP diagnostic message. -}
type Diagnostic =
  { severity :: Severity
  , message :: String
  , range ::
      { start :: { line :: Int, col :: Int }
      , end :: { line :: Int, col :: Int }
      }
  }

{-| Severity - Diagnostic severity level. -}
data Severity = Error | SevWarning | Info

derive instance eqSeverity :: Eq Severity

{-| Tactic - Suggested Lean4 proof tactic. -}
type Tactic =
  { tactic :: String
  , confidence :: Number
  }

-- ============================================================================
-- METRICS TYPES
-- ============================================================================

{-| Usage metrics - Application usage statistics.

Invariants:
- totalTokens >= 0
- totalCost >= 0.0
- averageResponseTime >= 0.0
- All tool timings have duration >= 0.0
-}
type UsageMetrics =
  { totalTokens :: Int
  , totalCost :: Number
  , averageResponseTime :: Number
  , toolTimings :: Array { tool :: String, duration :: Number }
  }

-- ============================================================================
-- APPLICATION STATE
-- ============================================================================

{-| Application state - Complete Bridge Server application state.

Invariants:
- All nested state slices maintain their own invariants
- connected reflects actual WebSocket connection status
- session is Nothing when no active session exists
-}
type AppState =
  { connected :: Boolean
  , balance :: BalanceState
  , session :: Maybe SessionState
  , proof :: ProofState
  , metrics :: UsageMetrics
  , alertConfig :: AlertConfig
  }

-- ============================================================================
-- STORE TYPES
-- ============================================================================

{-| State store - Mutable state container with change notifications.

Invariants:
- state always contains a valid AppState
- Listeners are called synchronously after state updates
- Listener order is deterministic (array order)
-}
type StateStore =
  { state :: Ref AppState
  , listeners :: Ref (Array (String -> String -> Effect Unit))
  }
