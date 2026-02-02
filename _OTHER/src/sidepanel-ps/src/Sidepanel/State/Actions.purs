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
import Sidepanel.State.AppState (AlertLevel, Panel, Theme, Goal, Diagnostic, Tactic, SnapshotSummary)

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
  
  -- Session
  | SessionUpdated SessionUpdate
  | SessionCleared
  | UsageRecorded UsageRecord
  
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
-- | - `consumptionRate`: Tokens consumed per hour
-- | - `timeToDepletion`: Hours until balance depletion (Nothing if sufficient)
-- | - `todayUsed`: Tokens used today
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
type BalanceUpdate =
  { diem :: Maybe Number      -- Venice Diem (optional)
  , flk :: Maybe Number       -- Fleek Token (optional)
  , usd :: Maybe Number       -- Venice USD (optional)
  , effective :: Number
  , consumptionRate :: Number
  , timeToDepletion :: Maybe Number
  , todayUsed :: Number
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
