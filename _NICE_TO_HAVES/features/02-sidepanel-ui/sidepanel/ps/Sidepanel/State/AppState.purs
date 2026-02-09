-- | Application State - Root State Type for Sidepanel Application
-- |
-- | **What:** Defines the root application state type containing all state slices
-- |         (connection, balance, session, proof, timeline, UI, settings, undo/redo).
-- |         This is the single source of truth for the sidepanel application state.
-- | **Why:** Provides a unified state structure that all components read from and
-- |         write to. Ensures consistent state across the entire application.
-- | **How:** Composed of multiple state slices, each managed by their respective
-- |         modules. State updates go through the reducer pattern (Sidepanel.State.Reducer).
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.Balance`: Balance state and calculations
-- | - `Sidepanel.State.UndoRedo`: Undo/redo history management
-- |
-- | **Mathematical Foundation:**
-- | - **State Invariant:** All nested state slices maintain their own invariants.
-- |   The root AppState is valid if all slices are valid.
-- | - **Initial State:** `initialState` provides a valid starting state with all
-- |   fields initialized to safe defaults.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.State.AppState as AppState
-- |
-- | -- Get initial state
-- | state :: AppState.AppState
-- | state = AppState.initialState
-- |
-- | -- Access state slices
-- | balance = state.balance
-- | session = state.session
-- | proof = state.proof
-- | ```
-- |
-- | Based on spec 41-STATE-MANAGEMENT.md
module Sidepanel.State.AppState where

import Prelude
import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Sidepanel.State.Balance (BalanceState, initialBalanceState)
import Sidepanel.State.UndoRedo (UndoRedoState, initialUndoRedoState)

-- | Root state type - Complete application state
-- |
-- | **Purpose:** The root state type containing all application state slices.
-- | **Fields:**
-- | - `connected`: WebSocket connection status
-- | - `lastSyncTime`: Last synchronization timestamp
-- | - `balance`: Balance state (all providers, Venice Diem)
-- | - `session`: Current active session (Nothing if no session)
-- | - `sessionHistory`: Array of past session summaries
-- | - `proof`: Lean4 proof state (connection, goals, diagnostics)
-- | - `snapshots`: Array of state snapshots for time-travel
-- | - `selectedSnapshotId`: Currently selected snapshot
-- | - `ui`: UI state (sidebar, panel, theme, alerts)
-- | - `settings`: Application settings
-- | - `undoRedo`: Undo/redo history state
-- |
-- | **Invariants:**
-- | - `selectedSnapshotId` is `Nothing` or refers to a snapshot in `snapshots`
-- | - `session` is `Nothing` when no active session exists
-- | - All nested state slices maintain their own invariants
-- |
-- | **Example:**
-- | ```purescript
-- | appState :: AppState
-- | appState = {
-- |   connected: true
-- |   , lastSyncTime: Just currentDateTime
-- |   , balance: balanceState
-- |   , session: Just sessionState
-- |   , sessionHistory: []
-- |   , proof: proofState
-- |   , snapshots: []
-- |   , selectedSnapshotId: Nothing
-- |   , ui: uiState
-- |   , settings: settingsState
-- |   , undoRedo: undoRedoState
-- | }
-- | ```
type AppState =
  { -- Connection
    connected :: Boolean
  , lastSyncTime :: Maybe DateTime
  
  -- Balance (all providers, Venice Diem included)
  , balance :: BalanceState
  
  -- Session
  , session :: Maybe SessionState
  , sessionHistory :: Array SessionSummary
  
  -- Proof (Lean4)
  , proof :: ProofState
  
  -- Timeline
  , snapshots :: Array SnapshotSummary
  , selectedSnapshotId :: Maybe String
  
  -- UI State
  , ui :: UIState
  
  -- Settings
  , settings :: Settings
  
  -- Undo/Redo
  , undoRedo :: UndoRedoState
  }

-- | Alert level - Balance depletion warning levels
-- |
-- | **Purpose:** Indicates the severity of balance depletion warnings.
-- | **Values:**
-- | - `Normal`: Balance is above warning threshold
-- | - `Warning`: Balance is below warning threshold but above critical
-- | - `Critical`: Balance is below critical threshold or time to depletion < 2 hours
-- | - `Depleted`: Balance is zero or negative
-- |
-- | **Invariant:** Alert level is calculated from balance thresholds, not set directly.
-- |              Use `calculateAlertLevel` function to compute from balance state.
data AlertLevel = Normal | Warning | Critical | Depleted

derive instance eqAlertLevel :: Eq AlertLevel
derive instance ordAlertLevel :: Ord AlertLevel

-- | Session state slice - Active chat session tracking
-- |
-- | **Purpose:** Tracks the current active chat session, including token usage,
-- |             cost, and model information.
-- | **Invariants:**
-- | - `totalTokens = promptTokens + completionTokens` (must be consistent)
-- | - `promptTokens >= 0` and `completionTokens >= 0` (cannot be negative)
-- | - `cost >= 0.0` (cannot be negative)
-- | - `messageCount >= 0` (cannot be negative)
-- |
-- | **Example:**
-- | ```purescript
-- | session :: SessionState
-- | session = {
-- |   id: "session-123"
-- |   , model: "gpt-4"
-- |   , promptTokens: 100
-- |   , completionTokens: 50
-- |   , totalTokens: 150
-- |   , cost: 0.0015
-- |   , messageCount: 5
-- |   , startedAt: startDateTime
-- | }
-- | ```
type SessionState =
  { id :: String
  , model :: String
  , promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cost :: Number
  , messageCount :: Int
  , startedAt :: DateTime
  }

-- | Session summary - Summary of a past session
-- |
-- | **Purpose:** Provides a lightweight summary of a session for display in
-- |             session history lists.
-- | **Fields:**
-- | - `id`: Session identifier
-- | - `model`: Model used in session
-- | - `cost`: Total cost of session
-- | - `tokenCount`: Total tokens used
-- | - `startedAt`: Session start timestamp
type SessionSummary =
  { id :: String
  , model :: String
  , cost :: Number
  , tokenCount :: Int
  , startedAt :: DateTime
  }

-- | Proof state (Lean4) - Lean4 LSP connection and proof status
-- |
-- | **Purpose:** Tracks the connection status to Lean4 LSP, current file being
-- |             edited, proof goals, diagnostics, and suggested tactics.
-- | **Invariants:**
-- | - `currentFile` is `Nothing` if `connected` is false (cannot have file without connection)
-- | - All arrays (goals, diagnostics, tactics) are valid and non-null
-- |
-- | **Example:**
-- | ```purescript
-- | proof :: ProofState
-- | proof = {
-- |   connected: true
-- |   , currentFile: Just "/path/to/File.lean"
-- |   , goals: [goal1, goal2]
-- |   , diagnostics: []
-- |   , suggestedTactics: [tactic1]
-- | }
-- | ```
type ProofState =
  { connected :: Boolean
  , currentFile :: Maybe String
  , goals :: Array Goal
  , diagnostics :: Array Diagnostic
  , suggestedTactics :: Array Tactic
  }

type Goal =
  { id :: String
  , type_ :: String
  , context :: String
  }

type Diagnostic =
  { severity :: String
  , message :: String
  , range :: Range
  }

type Range =
  { start :: Position
  , end :: Position
  }

type Position =
  { line :: Int
  , character :: Int
  }

type Tactic =
  { name :: String
  , description :: String
  , confidence :: Number
  }

-- | Snapshot for time-travel
type SnapshotSummary =
  { id :: String
  , timestamp :: DateTime
  , description :: String
  , stateHash :: String
  }

-- | UI state - User interface state
-- |
-- | **Purpose:** Tracks UI-specific state including sidebar visibility, active
-- |             panel, theme, and active alerts.
-- | **Fields:**
-- | - `sidebarCollapsed`: Whether sidebar is collapsed
-- | - `activePanel`: Currently active panel
-- | - `theme`: Current theme (Dark or Light)
-- | - `alerts`: Array of active alerts
type UIState =
  { sidebarCollapsed :: Boolean
  , activePanel :: Panel
  , theme :: Theme
  , alerts :: Array Alert
  }

-- | Panel - Available panels in the sidepanel
-- |
-- | **Purpose:** Represents the different panels/views available in the sidepanel.
-- | **Values:**
-- | - `DashboardPanel`: Main dashboard view
-- | - `SessionPanel`: Session detail view
-- | - `ProofPanel`: Lean4 proof assistant view
-- | - `TimelinePanel`: State timeline/snapshots view
-- | - `SettingsPanel`: Settings configuration view
-- | - `TerminalPanel`: Embedded terminal view
-- | - `FileContextPanel`: File context viewer
-- | - `DiffViewerPanel`: Diff viewer for file changes
data Panel
  = DashboardPanel
  | SessionPanel
  | ProofPanel
  | TimelinePanel
  | SettingsPanel
  | TerminalPanel
  | FileContextPanel
  | DiffViewerPanel

derive instance eqPanel :: Eq Panel

data Theme = Dark | Light

derive instance eqTheme :: Eq Theme

-- | Alert - User-facing alert notification
-- |
-- | **Purpose:** Represents an alert notification displayed to the user.
-- | **Fields:**
-- | - `id`: Unique alert identifier
-- | - `level`: Alert severity level
-- | - `message`: Alert message text
-- | - `timestamp`: When alert was triggered
type Alert =
  { id :: String
  , level :: AlertLevel
  , message :: String
  , timestamp :: DateTime
  }

-- | Settings (re-exported from Settings module for compatibility)
-- | Note: Full settings are in Sidepanel.State.Settings
type Settings =
  { veniceApiKey :: Maybe String
  , forgeApiUrl :: String
  , leanLspUrl :: Maybe String
  , monitorType :: MonitorType
  , blackBalance :: Number
  }

data MonitorType = OLED | LCD

derive instance eqMonitorType :: Eq MonitorType

-- | Initial state - Default application state
-- |
-- | **Purpose:** Creates the initial application state with all values set to
-- |             safe defaults. This is the starting state when the application loads.
-- | **Returns:** AppState with all fields initialized to defaults
-- | **Side Effects:** None (pure function)
-- |
-- | **Default Values:**
-- | - `connected: false` (not connected until WebSocket establishes)
-- | - `balance`: Initial balance state (all zeros, Normal alert level)
-- | - `session: Nothing` (no active session)
-- | - `proof`: Not connected, empty arrays
-- | - `snapshots`: Empty array
-- | - `ui`: Sidebar expanded, Dashboard panel, Dark theme, no alerts
-- | - `settings`: Default settings
-- | - `undoRedo`: History initialized with initial state
-- |
-- | **Example:**
-- | ```purescript
-- | initialState :: AppState
-- | initialState = AppState.initialState
-- | ```
initialState :: AppState
initialState =
  { connected: false
  , lastSyncTime: Nothing
  , balance: initialBalanceState
  , session: Nothing
  , sessionHistory: []
  , proof: initialProofState
  , snapshots: []
  , selectedSnapshotId: Nothing
  , ui: initialUIState
  , settings: initialSettings
  , undoRedo: initialUndoRedoState initialState
  }

-- Initial balance state imported from Balance module

initialProofState :: ProofState
initialProofState =
  { connected: false
  , currentFile: Nothing
  , goals: []
  , diagnostics: []
  , suggestedTactics: []
  }

-- | Initial UI state - Default UI state
-- |
-- | **Purpose:** Creates the initial UI state with sidebar expanded, dashboard
-- |             panel active, dark theme, and no alerts.
-- | **Returns:** UIState with all fields initialized to defaults
-- | **Side Effects:** None (pure function)
initialUIState :: UIState
initialUIState =
  { sidebarCollapsed: false
  , activePanel: DashboardPanel
  , theme: Dark
  , alerts: []
  }

-- | Initial settings - Default application settings
-- |
-- | **Purpose:** Creates the initial settings with default values for all
-- |             configuration options.
-- | **Returns:** Settings with all fields initialized to defaults
-- | **Side Effects:** None (pure function)
-- |
-- | **Default Values:**
-- | - `veniceApiKey: Nothing` (must be configured by user)
-- | - `forgeApiUrl: "http://localhost:4096"` (default Forge server)
-- | - `leanLspUrl: Nothing` (must be configured if Lean4 support needed)
-- | - `monitorType: OLED` (default to OLED for better contrast)
-- | - `blackBalance: 0.11` (default OLED black level)
initialSettings :: Settings
initialSettings =
  { veniceApiKey: Nothing
  , forgeApiUrl: "http://localhost:4096"
  , leanLspUrl: Nothing
  , monitorType: OLED
  , blackBalance: 0.11
  }
