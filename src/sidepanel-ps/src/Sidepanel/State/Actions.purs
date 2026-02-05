-- | State Actions - All Possible State Transition Actions
-- |
-- | **What:** Defines all possible actions that can be dispatched to update
-- |         application state. Actions are processed by the reducer (Sidepanel.State.Reducer)
-- |         to produce new state.
-- | **Why:** Provides a type-safe way to represent all state transitions. Ensures
-- |         all state changes go through the reducer pattern for predictability and
-- |         undo/redo support.
-- | **How:** Actions are dispatched from components or event handlers, processed
-- |         by the reducer, and result in new state. Undo/Redo actions restore
-- |         previous states from history.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.AppState`: Uses types from AppState (AlertLevel, Panel, etc.)
-- |
-- | **Mathematical Foundation:**
-- | - **Action Categories:**
-- |   - Connection: `Connected`, `Disconnected`, `PingReceived`
-- |   - Balance: `BalanceUpdated`, `CountdownTick`, `AlertLevelChanged`
-- |   - Session: `SessionUpdated`, `SessionCleared`, `UsageRecorded`
-- |   - Proof: `ProofConnected`, `ProofDisconnected`, `GoalsUpdated`, etc.
-- |   - Timeline: `SnapshotCreated`, `SnapshotSelected`, `SnapshotRestored`
-- |   - UI: `ToggleSidebar`, `SetActivePanel`, `SetTheme`, `DismissAlert`
-- |   - Alerts: `AlertTriggered`
-- |   - Undo/Redo: `Undo`, `Redo`
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.State.Actions as Actions
-- | import Sidepanel.State.Reducer as Reducer
-- |
-- | -- Dispatch action
-- | newState = Reducer.reduce currentState Actions.Connected
-- |
-- | -- Update balance
-- | update = { diem: 1000.0, usd: 10.0, ... }
-- | newState = Reducer.reduce currentState (Actions.BalanceUpdated update)
-- | ```
-- |
-- | Based on spec 41-STATE-MANAGEMENT.md
module Sidepanel.State.Actions where

import Prelude
import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Sidepanel.State.AppState (AlertLevel, Panel, Theme, Goal, Diagnostic, Tactic, SnapshotSummary, Message)
import Sidepanel.State.RateLimit (RateLimitHeaders)
import Sidepanel.State.Sessions (SessionStatus)

-- | All possible state actions - Sum type of all state transitions
-- |
-- | **Purpose:** Represents all possible actions that can be dispatched to update
-- |             application state. Each constructor represents a different type of
-- |             state transition.
-- | **Action Categories:**
-- | - **Connection:** `Connected`, `Disconnected`, `PingReceived`
-- | - **Balance:** `BalanceUpdated`, `CountdownTick`, `AlertLevelChanged`
-- | - **Session:** `SessionUpdated`, `SessionCleared`, `UsageRecorded`
-- | - **Proof:** `ProofConnected`, `ProofDisconnected`, `GoalsUpdated`, `DiagnosticsUpdated`, `TacticsUpdated`
-- | - **Timeline:** `SnapshotCreated`, `SnapshotSelected`, `SnapshotRestored`
-- | - **UI:** `ToggleSidebar`, `SetActivePanel`, `SetTheme`, `DismissAlert`
-- | - **Alerts:** `AlertTriggered`
-- | - **Undo/Redo:** `Undo`, `Redo`
data Action
  -- Connection
  = Connected
  | Disconnected
  | PingReceived DateTime
  
  -- Balance (Venice Diem)
  | BalanceUpdated BalanceUpdate
  | CountdownTick
  | AlertLevelChanged AlertLevel
  
  -- Rate Limits (Venice API)
  | RateLimitUpdated RateLimitHeaders
  | RateLimitHit Number  -- retryAfterSeconds
  | RateLimitBackoffTick  -- Decrement backoff timer
  
  -- Session (Legacy single-session)
  | SessionUpdated SessionUpdate
  | SessionCleared
  | UsageRecorded UsageRecord
  | MessageAdded Message  -- DEPRECATED: Use MessageAddedToSession
  | MessagesCleared  -- DEPRECATED: Use MessagesClearedForSession
  
  -- Multi-Session Management
  | SessionOpened String String String  -- sessionId, title, icon
  | SessionClosed String  -- sessionId
  | SessionSwitched String  -- sessionId
  | TabsReordered (Array String)  -- New tab order (session IDs)
  | TabPinned String  -- sessionId
  | TabUnpinned String  -- sessionId
  | TabRenamed String String  -- sessionId, newTitle
  | TabIconSet String String  -- sessionId, newIcon
  | SessionCreated SessionUpdate String String  -- sessionUpdate, title, icon (creates new session)
  | SessionBranchCreated String Int String String String  -- parentSessionId, messageIndex, description, branchSessionId, branchTitle
  | SessionBranchMerged String String  -- sourceSessionId, targetSessionId
  | MessageAddedToSession String Message  -- sessionId, message
  | MessagesClearedForSession String  -- sessionId
  | SessionMetadataUpdated String SessionMetadataUpdate  -- sessionId, metadata update
  
  -- Proof (Lean4)
  | ProofConnected
  | ProofDisconnected
  | GoalsUpdated (Array Goal)
  | DiagnosticsUpdated (Array Diagnostic)
  | TacticsUpdated (Array Tactic)
  
  -- Timeline
  | SnapshotCreated SnapshotSummary
  | SnapshotSelected String
  | SnapshotRestored String
  
  -- UI
  | ToggleSidebar
  | SetActivePanel Panel
  | SetTheme Theme
  | DismissAlert String
  
  -- Alerts
  | AlertTriggered AlertData
  
  -- Undo/Redo
  | Undo
  | Redo

-- | Balance update payload - Data for balance updates
-- |
-- | **Purpose:** Contains balance update data for the `BalanceUpdated` action.
-- | **Fields:**
-- | - `diem`: Venice Diem balance (optional, for Venice updates)
-- | - `flk`: Fleek Token (FLK) balance (optional, for FLK updates)
-- | - `usd`: USD balance (optional, for Venice updates)
-- | - `effective`: Effective balance (Diem + USD for Venice, or FLK for FLK)
-- | - `consumptionRate`: Tokens consumed per hour (from server, but will be recalculated from history)
-- | - `timeToDepletion`: Hours until balance depletion (from server, but will be recalculated)
-- | - `todayUsed`: Tokens used today
-- | - `timestamp`: Timestamp of the balance update (for history tracking)
-- |
-- | **Invariants:**
-- | - `diem >= 0.0` (cannot be negative, if provided)
-- | - `flk >= 0.0` (cannot be negative, if provided)
-- | - `usd >= 0.0` (cannot be negative, if provided)
-- | - `effective >= 0.0` (cannot be negative)
-- | - `consumptionRate >= 0.0` (cannot be negative)
-- | - `todayUsed >= 0.0` (cannot be negative)
-- |
-- | **Note:** Either Venice fields (diem/usd) or FLK field should be provided, not both.
-- | **Note:** Consumption rate and time-to-depletion are calculated client-side from history,
-- |          but server-provided values are included for fallback/verification.
type BalanceUpdate =
  { diem :: Maybe Number      -- Venice Diem (optional)
  , flk :: Maybe Number       -- Fleek Token (optional)
  , usd :: Maybe Number       -- Venice USD (optional)
  , effective :: Number
  , consumptionRate :: Number  -- From server (fallback), recalculated from history
  , timeToDepletion :: Maybe Number  -- From server (fallback), recalculated from history
  , todayUsed :: Number
  , timestamp :: Maybe DateTime  -- Timestamp of update (for history)
  }

-- | Session update payload - Data for session updates
-- |
-- | **Purpose:** Contains session update data for the `SessionUpdated` action.
-- | **Fields:**
-- | - `id`: Session identifier
-- | - `model`: Model name (e.g., "gpt-4")
-- | - `promptTokens`: Prompt tokens used
-- | - `completionTokens`: Completion tokens used
-- | - `totalTokens`: Total tokens (should equal prompt + completion)
-- | - `cost`: Session cost in USD
-- | - `messageCount`: Number of messages in session
-- | - `startedAt`: Optional session start time (Nothing uses existing or current time)
-- |
-- | **Invariants:**
-- | - `totalTokens = promptTokens + completionTokens` (must be consistent)
-- | - `promptTokens >= 0` and `completionTokens >= 0`
-- | - `cost >= 0.0`
-- | - `messageCount >= 0`
type SessionUpdate =
  { id :: String
  , model :: String
  , promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cost :: Number
  , messageCount :: Int
  , startedAt :: Maybe DateTime  -- Optional - if Nothing, use existing or current time
  }

-- | Usage record
type UsageRecord =
  { prompt :: Int
  , completion :: Int
  , cost :: Number
  }

-- | Alert data - Alert notification data
-- |
-- | **Purpose:** Contains alert data for the `AlertTriggered` action.
-- | **Fields:**
-- | - `level`: Alert severity level
-- | - `message`: Alert message text
-- | - `timestamp`: When alert was triggered
type AlertData =
  { level :: AlertLevel
  , message :: String
  , timestamp :: DateTime
  }

-- | Session metadata update - Partial update for session metadata
-- |
-- | **Purpose:** Allows partial updates to session metadata without requiring all fields.
-- | **Fields:** All optional - only provided fields are updated
type SessionMetadataUpdate =
  { title :: Maybe String
  , icon :: Maybe String
  , color :: Maybe (Maybe String)  -- Maybe (Maybe String) to distinguish "set to Nothing" from "no change"
  , status :: Maybe SessionStatus
  , parentId :: Maybe (Maybe String)
  , branchPoint :: Maybe (Maybe Int)
  , children :: Maybe (Array String)
  }
