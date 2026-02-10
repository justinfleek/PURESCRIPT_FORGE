-- | Bridge State Store Types
-- | Core application state types for the bridge server
module Bridge.State.Store.Types where

import Prelude
import Effect (Effect)
import Effect.Ref (Ref)
import Data.Maybe (Maybe)

-- | Alert severity level
data AlertLevel = Normal | Warning | Critical

derive instance eqAlertLevel :: Eq AlertLevel

instance showAlertLevel :: Show AlertLevel where
  show Normal = "normal"
  show Warning = "warning"
  show Critical = "critical"

-- | Alert configuration thresholds
type AlertConfig =
  { diemWarningPercent :: Number
  , diemCriticalPercent :: Number
  , depletionWarningHours :: Number
  }

-- | Balance state
type BalanceState =
  { venice ::
      { diem :: Number
      , usd :: Number
      , effective :: Number
      , lastUpdated :: Maybe Number
      }
  , consumptionRate :: Number
  , timeToDepletion :: Maybe Number
  , todayUsed :: Number
  , todayStartBalance :: Number
  , resetCountdown :: Maybe Number
  , alertLevel :: AlertLevel
  }

-- | Session state
type SessionState =
  { id :: String
  , promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cost :: Number
  , model :: String
  , provider :: String
  , messageCount :: Int
  , startedAt :: Number
  , updatedAt :: Number
  }

-- | Lean4 proof goal
type Goal =
  { type_ :: String
  , context :: Array { name :: String, type_ :: String }
  }

-- | Diagnostic severity
data Severity = Error | SevWarning | Info

derive instance eqSeverity :: Eq Severity

instance showSeverity :: Show Severity where
  show Error = "error"
  show SevWarning = "warning"
  show Info = "info"

-- | Lean4 diagnostic
type Diagnostic =
  { severity :: Severity
  , message :: String
  , range ::
      { start :: { line :: Int, col :: Int }
      , end :: { line :: Int, col :: Int }
      }
  }

-- | Lean4 tactic suggestion
type Tactic =
  { tactic :: String
  , confidence :: Number
  }

-- | Lean4 proof state
type ProofState =
  { connected :: Boolean
  , file :: Maybe String
  , position :: Maybe { line :: Int, column :: Int }
  , goals :: Array Goal
  , diagnostics :: Array Diagnostic
  , suggestedTactics :: Array Tactic
  }

-- | Usage metrics
type UsageMetrics =
  { totalTokens :: Int
  , totalCost :: Number
  , averageResponseTime :: Number
  , toolTimings :: Array { tool :: String, duration :: Number }
  }

-- | Complete application state
type AppState =
  { connected :: Boolean
  , balance :: BalanceState
  , session :: Maybe SessionState
  , proof :: ProofState
  , metrics :: UsageMetrics
  , alertConfig :: AlertConfig
  }

-- | Mutable state store with listener support
type StateStore =
  { state :: Ref AppState
  , listeners :: Ref (Array (String -> String -> Effect Unit))
  }
