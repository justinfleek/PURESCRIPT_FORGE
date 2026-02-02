-- | Bridge API Types
-- |
-- | Type definitions and JSON codecs for bridge server API communication.
-- |
-- | Coeffect Equation:
-- |   Types : Type^n -> Codec^n
-- |   where Type^n represents n distinct API types
-- |   and Codec^n their JSON serialization instances
-- |
-- | Module Coverage: Request/response types for all bridge API endpoints
module Sidepanel.Api.Bridge.Types
  ( -- * File Context Types
    FileContextAddRequest
  , FileContextAddResponse
  , FileContextListRequest
  , FileContextListResponse
  , FileInContext
  , FileReadRequest
  , FileReadResponse
  , FileContextEntry
    -- * Terminal Types
  , TerminalExecuteRequest
  , TerminalExecuteResponse
    -- * Session Types
  , SessionNewRequest
  , SessionNewResponse
  , SessionState
    -- * Snapshot Types
  , SnapshotListRequest
  , SnapshotListResponse
  , SnapshotSummary
  , SnapshotSaveRequest
  , SnapshotSaveResponse
  , SnapshotRestoreRequest
  , SnapshotRestoreResponse
  , SnapshotGetRequest
  , SnapshotGetResponse
  , SnapshotGetState
    -- * Balance/Metrics Types
  , BalanceState
  , ProofState
  , UsageMetrics
    -- * Lean Types
  , LeanCheckRequest
  , LeanCheckResponse
  , LeanDiagnostic
  , LeanGoalsRequest
  , LeanGoalsResponse
  , LeanGoal
  , LeanApplyTacticRequest
  , LeanApplyTacticResponse
  , LeanSearchTheoremsRequest
  , LeanSearchTheoremsResponse
  , TheoremResult
    -- * Settings Types
  , SettingsSaveRequest
  , SettingsSaveResponse
    -- * Utilities
  , printJsonDecodeError
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.DateTime (DateTime)
import Data.Argonaut.Decode.Error (JsonDecodeError)

--------------------------------------------------------------------------------
-- | Utility Functions
--------------------------------------------------------------------------------

-- | Convert JSON decode error to string
printJsonDecodeError :: JsonDecodeError -> String
printJsonDecodeError err = show err

--------------------------------------------------------------------------------
-- | File Context Types
--------------------------------------------------------------------------------

-- | File context add request
type FileContextAddRequest =
  { path :: String
  , sessionId :: Maybe String
  }

-- | File context add response
type FileContextAddResponse =
  { success :: Boolean
  , tokens :: Int
  , contextBudget ::
      { used :: Int
      , total :: Int
      }
  }

-- | File context list request
type FileContextListRequest =
  { sessionId :: Maybe String
  , filter :: Maybe String
  }

-- | File in context
type FileInContext =
  { path :: String
  , tokens :: Int
  , readAt :: Number
  , status :: String
  , language :: String
  , size :: Int
  }

-- | File context list response
type FileContextListResponse =
  { files :: Array FileInContext
  , contextBudget ::
      { used :: Int
      , total :: Int
      }
  }

-- | File read request
type FileReadRequest =
  { path :: String
  }

-- | File read response
type FileReadResponse =
  { success :: Boolean
  , content :: Maybe String
  , error :: Maybe String
  }

-- | File context entry (simplified)
type FileContextEntry =
  { path :: String
  , tokens :: Int
  , language :: String
  }

--------------------------------------------------------------------------------
-- | Terminal Types
--------------------------------------------------------------------------------

-- | Terminal execute request
type TerminalExecuteRequest =
  { command :: String
  , cwd :: Maybe String
  , sessionId :: Maybe String
  }

-- | Terminal execute response
type TerminalExecuteResponse =
  { success :: Boolean
  , output :: Maybe String
  , exitCode :: Maybe Int
  }

--------------------------------------------------------------------------------
-- | Session Types
--------------------------------------------------------------------------------

-- | Session new request
type SessionNewRequest =
  { name :: Maybe String
  , parentId :: Maybe String
  , model :: Maybe String
  , provider :: Maybe String
  }

-- | Session new response
type SessionNewResponse =
  { sessionId :: String
  , success :: Boolean
  }

-- | Session state (placeholder for full session)
type SessionState = 
  { id :: String
  , name :: Maybe String
  , model :: String
  , provider :: String
  }

--------------------------------------------------------------------------------
-- | Snapshot Types
--------------------------------------------------------------------------------

-- | Snapshot list request
type SnapshotListRequest =
  { limit :: Maybe Int
  , offset :: Maybe Int
  }

-- | Snapshot summary
type SnapshotSummary =
  { id :: String
  , timestamp :: String  -- ISO 8601 string
  , description :: Maybe String
  }

-- | Snapshot list response
type SnapshotListResponse =
  { snapshots :: Array SnapshotSummary
  }

-- | Snapshot save request
type SnapshotSaveRequest =
  { trigger :: String
  , description :: Maybe String
  }

-- | Snapshot save response
type SnapshotSaveResponse =
  { id :: String
  , success :: Boolean
  }

-- | Snapshot restore request
type SnapshotRestoreRequest =
  { id :: String
  }

-- | Snapshot restore response
type SnapshotRestoreResponse =
  { success :: Boolean
  }

-- | Snapshot get request
type SnapshotGetRequest =
  { id :: String
  }

-- | Snapshot get response
type SnapshotGetResponse =
  { id :: String
  , timestamp :: String
  , description :: Maybe String
  , state :: SnapshotGetState
  }

-- | Snapshot state container
type SnapshotGetState =
  { balance :: Maybe BalanceState
  , session :: Maybe SessionState
  , proof :: Maybe ProofState
  , metrics :: Maybe UsageMetrics
  , fileContext :: Array FileContextEntry
  }

--------------------------------------------------------------------------------
-- | Balance/Metrics Types
--------------------------------------------------------------------------------

-- | Balance state
type BalanceState =
  { venice :: { diem :: Number, usd :: Number, effective :: Number, lastUpdated :: Maybe DateTime }
  , consumptionRate :: Number
  , timeToDepletion :: Maybe Int
  , todayUsed :: Number
  , todayStartBalance :: Number
  , resetCountdown :: Maybe Int
  , alertLevel :: String
  }

-- | Proof assistant state
type ProofState =
  { connected :: Boolean
  , file :: Maybe String
  , position :: Maybe { line :: Int, col :: Int }
  , goals :: Array { type_ :: String, context :: Array { name :: String, type_ :: String } }
  , diagnostics :: Array { severity :: String, message :: String, range :: { start :: { line :: Int, col :: Int }, end :: { line :: Int, col :: Int } } }
  , suggestedTactics :: Array { name :: String, description :: String, confidence :: Number }
  }

-- | Usage metrics
type UsageMetrics =
  { totalTokens :: Int
  , totalCost :: Number
  , averageResponseTime :: Number
  , toolTimings :: Array { name :: String, duration :: Number }
  }

--------------------------------------------------------------------------------
-- | Lean Types
--------------------------------------------------------------------------------

-- | Lean check request
type LeanCheckRequest =
  { file :: String
  }

-- | Lean diagnostic
type LeanDiagnostic =
  { severity :: String
  , message :: String
  , range ::
      { start :: { line :: Int, col :: Int }
      , end :: { line :: Int, col :: Int }
      }
  }

-- | Lean check response
type LeanCheckResponse =
  { diagnostics :: Array LeanDiagnostic
  }

-- | Lean goals request
type LeanGoalsRequest =
  { file :: String
  , line :: Int
  , column :: Int
  }

-- | Lean goal
type LeanGoal =
  { type_ :: String
  , context :: Array { name :: String, type_ :: String }
  }

-- | Lean goals response
type LeanGoalsResponse =
  { goals :: Array LeanGoal
  }

-- | Apply Lean tactic request
type LeanApplyTacticRequest =
  { file :: String
  , line :: Int
  , column :: Int
  , tactic :: String
  , goalIndex :: Maybe Int
  }

-- | Apply Lean tactic response
type LeanApplyTacticResponse =
  { success :: Boolean
  , message :: Maybe String
  , goals :: Array LeanGoal
  }

-- | Search Lean theorems request
type LeanSearchTheoremsRequest =
  { query :: String
  , limit :: Maybe Int
  , file :: Maybe String
  }

-- | Theorem search result
type TheoremResult =
  { name :: String
  , statement :: String
  , file :: String
  , line :: Int
  , description :: Maybe String
  }

-- | Search Lean theorems response
type LeanSearchTheoremsResponse =
  { theorems :: Array TheoremResult
  , total :: Int
  }

--------------------------------------------------------------------------------
-- | Settings Types
--------------------------------------------------------------------------------

-- | Settings save request (matches Settings type from Sidepanel.State.Settings)
type SettingsSaveRequest =
  { alerts ::
      { warningPercent :: Number
      , criticalPercent :: Number
      , warningHours :: Number
      , soundEnabled :: Boolean
      }
  , appearance ::
      { theme :: String
      }
  , keyboard ::
      { enabled :: Boolean
      , vimMode :: Boolean
      }
  , features ::
      { countdown :: Boolean
      , tokenCharts :: Boolean
      , proofPanel :: Boolean
      , timeline :: Boolean
      }
  , storage ::
      { retentionDays :: Int
      }
  }

-- | Settings save response
type SettingsSaveResponse =
  { success :: Boolean
  }
