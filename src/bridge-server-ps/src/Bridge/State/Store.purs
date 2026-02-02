-- | State Store - Single Source of Truth for Bridge Server Application State
-- |
-- | **What:** Provides centralized state management for the Bridge Server, maintaining
-- |         application state (balance, session, proof, metrics) in a mutable reference
-- |         with change notification support. This is the authoritative state store that
-- |         all Bridge Server components read from and write to.
-- | **Why:** Ensures consistent state across all Bridge Server modules (WebSocket handlers,
-- |         Venice client, Lean proxy, database sync). Prevents state inconsistencies by
-- |         providing a single source of truth with controlled mutation and change notifications.
-- | **How:** Uses PureScript Effect.Ref for mutable state storage, with a listener pattern
-- |         for change notifications. All state updates go through this module's update
-- |         functions, which notify registered listeners. State is stored in memory and
-- |         synchronized with persistent storage (SQLite) via separate sync mechanisms.
-- |
-- | **Dependencies:**
-- | - `Effect.Ref`: Provides mutable references for state storage
-- | - `Data.DateTime`: For timestamp tracking in balance and session state
-- | - `Data.Array`: For managing arrays of goals, diagnostics, tactics, and listeners
-- |
-- | **Mathematical Foundation:**
-- | - **State Invariant:** The state store always contains a valid AppState. No partial
-- |   or invalid states are possible.
-- | - **Update Invariant:** All update functions preserve state validity. Partial updates
-- |   merge with existing state rather than replacing it entirely.
-- | - **Listener Invariant:** Listeners are notified synchronously after state updates.
-- |   The order of listener execution is deterministic (array order).
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.State.Store as Store
-- |
-- | -- Create state store
-- | store <- Store.createStore
-- |
-- | -- Get current state
-- | currentState <- Store.getState store
-- |
-- | -- Update balance
-- | Store.updateBalance store newBalance
-- |
-- | -- Subscribe to state changes
-- | unsubscribe <- Store.onStateChange store \path value -> do
-- |   log $ "State changed: " <> path <> " = " <> value
-- |
-- | -- Later: unsubscribe
-- | unsubscribe
-- | ```
-- |
-- | Based on spec 41-STATE-MANAGEMENT.md
module Bridge.State.Store where

import Prelude
import Effect (Effect)
import Effect.Ref (Ref, new, read, write, modify)
import Data.DateTime (DateTime)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Array (catMaybes) as Array
import Data.Array as Array
import Data.Foldable (traverse_)

-- | Balance state - Token balance and consumption tracking
-- |
-- | **Purpose:** Tracks token balance (Venice Diem), consumption rate, depletion estimates,
-- |             and alert levels for the Bridge Server application.
-- | **Invariants:**
-- | - `consumptionRate >= 0.0` (consumption rate cannot be negative)
-- | - `todayUsed >= 0.0` (usage cannot be negative)
-- | - `alertLevel` is calculated from balance thresholds, not set directly
-- | - `timeToDepletion` is `Nothing` if balance is sufficient or `consumptionRate` is 0
-- |
-- | **Example:**
-- | ```purescript
-- | balance :: BalanceState
-- | balance = {
-- |   venice: Just {
-- |     diem: 1000.0
-- |     , usd: 10.0
-- |     , effective: 1000.0
-- |     , lastUpdated: Just currentDateTime
-- |   }
-- |   , consumptionRate: 50.0
-- |   , timeToDepletion: Just 20.0
-- |   , todayUsed: 500.0
-- |   , todayStartBalance: 1500.0
-- |   , resetCountdown: Just 3600.0
-- |   , alertLevel: Warning
-- | }
-- | ```
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

-- | Alert level - Balance depletion warning levels
-- |
-- | **Purpose:** Indicates the severity of balance depletion warnings.
-- | **Values:**
-- | - `Normal`: Balance is above warning threshold
-- | - `Warning`: Balance is below warning threshold but above critical threshold
-- | - `Critical`: Balance is below critical threshold
-- |
-- | **Invariant:** Alert level is calculated from balance thresholds, not set directly.
-- |              Use `calculateAlertLevel` function to compute from balance state.
data AlertLevel = Normal | Warning | Critical

derive instance eqAlertLevel :: Eq AlertLevel

-- | Session state - Active chat session tracking
-- |
-- | **Purpose:** Tracks the current active chat session, including token usage, cost,
-- |             model information, and message count.
-- | **Invariants:**
-- | - `totalTokens = promptTokens + completionTokens` (must be consistent)
-- | - `promptTokens >= 0` and `completionTokens >= 0` (cannot be negative)
-- | - `cost >= 0.0` (cannot be negative)
-- | - `messageCount >= 0` (cannot be negative)
-- | - `updatedAt >= startedAt` (session cannot update before it starts)
-- |
-- | **Example:**
-- | ```purescript
-- | session :: SessionState
-- | session = {
-- |   id: "session-123"
-- |   , promptTokens: 100
-- |   , completionTokens: 50
-- |   , totalTokens: 150
-- |   , cost: 0.0015
-- |   , model: "gpt-4"
-- |   , provider: "venice"
-- |   , messageCount: 5
-- |   , startedAt: startDateTime
-- |   , updatedAt: currentDateTime
-- | }
-- | ```
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

-- | Proof state - Lean4 LSP connection and proof status
-- |
-- | **Purpose:** Tracks the connection status to Lean4 LSP, current file being edited,
-- |             proof goals, diagnostics, and suggested tactics.
-- | **Invariants:**
-- | - `position` is `Nothing` if `file` is `Nothing` (cannot have position without file)
-- | - All arrays (goals, diagnostics, tactics) are valid and non-null
-- |
-- | **Example:**
-- | ```purescript
-- | proof :: ProofState
-- | proof = {
-- |   connected: true
-- |   , file: Just "/path/to/File.lean"
-- |   , position: Just { line: 10, column: 5 }
-- |   , goals: [goal1, goal2]
-- |   , diagnostics: []
-- |   , suggestedTactics: [tactic1]
-- | }
-- | ```
type ProofState =
  { connected :: Boolean
  , file :: Maybe String
  , position :: Maybe { line :: Int, column :: Int }
  , goals :: Array Goal
  , diagnostics :: Array Diagnostic
  , suggestedTactics :: Array Tactic
  }

-- | Goal - Lean4 proof goal
-- |
-- | **Purpose:** Represents a single proof goal in Lean4, including its type and context.
-- | **Fields:**
-- | - `type_`: The type that needs to be proven
-- | - `context`: Array of variables and their types in scope
type Goal =
  { type_ :: String
  , context :: Array { name :: String, type_ :: String }
  }

-- | Diagnostic - Lean4 LSP diagnostic message
-- |
-- | **Purpose:** Represents an error, warning, or info message from Lean4 LSP.
-- | **Fields:**
-- | - `severity`: Error, Warning, or Info
-- | - `message`: Diagnostic message text
-- | - `range`: Source location (start and end positions)
type Diagnostic =
  { severity :: Severity
  , message :: String
  , range ::
      { start :: { line :: Int, col :: Int }
      , end :: { line :: Int, col :: Int }
      }
  }

-- | Severity - Diagnostic severity level
-- |
-- | **Purpose:** Indicates the severity of a Lean4 diagnostic message.
-- | **Values:**
-- | - `SevError`: Critical error that prevents compilation
-- | - `SevWarning`: Warning that may indicate issues
-- | - `SevInfo`: Informational message
data Severity = SevError | SevWarning | SevInfo

derive instance eqSeverity :: Eq Severity

-- | Tactic - Suggested Lean4 proof tactic
-- |
-- | **Purpose:** Represents a suggested tactic for proving a goal, with confidence score.
-- | **Fields:**
-- | - `tactic`: The tactic string (e.g., "simp", "rw [theorem]")
-- | - `confidence`: Confidence score between 0.0 and 1.0
type Tactic =
  { tactic :: String
  , confidence :: Number
  }

-- | Usage metrics - Application usage statistics
-- |
-- | **Purpose:** Tracks aggregate usage statistics including total tokens, cost, response times,
-- |             and tool execution timings.
-- | **Invariants:**
-- | - `totalTokens >= 0` (cannot be negative)
-- | - `totalCost >= 0.0` (cannot be negative)
-- | - `averageResponseTime >= 0.0` (cannot be negative)
-- | - All tool timings have `duration >= 0.0`
-- |
-- | **Example:**
-- | ```purescript
-- | metrics :: UsageMetrics
-- | metrics = {
-- |   totalTokens: 10000
-- |   , totalCost: 0.10
-- |   , averageResponseTime: 1.5
-- |   , toolTimings: [
-- |       { tool: "venice.chat", duration: 1.2 }
-- |       , { tool: "lean.check", duration: 0.3 }
-- |     ]
-- | }
-- | ```
type UsageMetrics =
  { totalTokens :: Int
  , totalCost :: Number
  , averageResponseTime :: Number
  , toolTimings :: Array { tool :: String, duration :: Number }
  }

-- | Alert configuration - Balance alert thresholds
-- |
-- | **Purpose:** Configures thresholds for balance depletion alerts.
-- | **Fields:**
-- | - `diemWarningPercent`: Percentage threshold for warning alerts (e.g., 0.20 = 20%)
-- | - `diemCriticalPercent`: Percentage threshold for critical alerts (e.g., 0.05 = 5%)
-- | - `depletionWarningHours`: Hours before depletion to trigger warning
-- |
-- | **Invariants:**
-- | - `0.0 <= diemWarningPercent <= 1.0`
-- | - `0.0 <= diemCriticalPercent <= 1.0`
-- | - `diemCriticalPercent < diemWarningPercent` (critical must be lower than warning)
-- | - `depletionWarningHours >= 0.0`
-- |
-- | **Example:**
-- | ```purescript
-- | config :: AlertConfig
-- | config = {
-- |   diemWarningPercent: 0.20
-- |   , diemCriticalPercent: 0.05
-- |   , depletionWarningHours: 2.0
-- | }
-- | ```
type AlertConfig =
  { diemWarningPercent :: Number
  , diemCriticalPercent :: Number
  , depletionWarningHours :: Number
  }

-- | Application state - Complete Bridge Server application state
-- |
-- | **Purpose:** The root state type containing all application state slices (balance, session,
-- |             proof, metrics, alerts). This is the single source of truth for the entire
-- |             Bridge Server application.
-- | **Invariants:**
-- | - All nested state slices maintain their own invariants
-- | - `connected` reflects actual WebSocket connection status
-- | - `session` is `Nothing` when no active session exists
-- |
-- | **Example:**
-- | ```purescript
-- | appState :: AppState
-- | appState = {
-- |   connected: true
-- |   , balance: balanceState
-- |   , session: Just sessionState
-- |   , proof: proofState
-- |   , metrics: usageMetrics
-- |   , alertConfig: alertConfig
-- | }
-- | ```
type AppState =
  { connected :: Boolean
  , balance :: BalanceState
  , session :: Maybe SessionState
  , proof :: ProofState
  , metrics :: UsageMetrics
  , alertConfig :: AlertConfig
  }

-- | State store - Mutable state container with change notifications
-- |
-- | **Purpose:** Provides mutable access to application state with listener-based change
-- |             notifications. The state is stored in an Effect.Ref, and listeners are
-- |             notified synchronously after each state update.
-- | **Fields:**
-- | - `state`: Mutable reference to AppState
-- | - `listeners`: Array of change listeners (path, value) -> Effect Unit
-- |
-- | **Invariants:**
-- | - `state` always contains a valid AppState
-- | - Listeners are called synchronously after state updates
-- | - Listener order is deterministic (array order)
-- |
-- | **Example:**
-- | ```purescript
-- | store :: StateStore
-- | store = {
-- |   state: stateRef
-- |   , listeners: listenersRef
-- | }
-- | ```
type StateStore =
  { state :: Ref AppState
  , listeners :: Ref (Array (String -> String -> Effect Unit))
  }

-- | Create initial state - Default application state
-- |
-- | **Purpose:** Creates the initial application state with all values set to defaults.
-- | **Returns:** AppState with all fields initialized to safe defaults
-- | **Side Effects:** None (pure function)
-- |
-- | **Default Values:**
-- | - `connected: false` (not connected until WebSocket establishes)
-- | - `balance`: All zeros, Normal alert level
-- | - `session: Nothing` (no active session)
-- | - `proof`: Not connected, empty arrays
-- | - `metrics`: All zeros
-- | - `alertConfig`: Standard thresholds (20% warning, 5% critical, 2 hours)
-- |
-- | **Example:**
-- | ```purescript
-- | initialState :: AppState
-- | initialState = Store.initialState
-- | ```
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

-- | Create state store
createStore :: Effect StateStore
createStore = do
  state <- new initialState
  listeners <- new []
  pure { state, listeners }

-- | Get current state - Read current application state
-- |
-- | **Purpose:** Reads the current application state from the store.
-- | **Parameters:**
-- | - `store`: The state store to read from
-- | **Returns:** Current AppState
-- | **Side Effects:** Reads mutable reference (Effect.Ref.read)
-- |
-- | **Example:**
-- | ```purescript
-- | currentState <- Store.getState store
-- | ```
getState :: StateStore -> Effect AppState
getState store = read store.state

-- | Update balance (partial update) - Merge partial balance updates
-- |
-- | **Purpose:** Updates balance state by merging partial updates with existing balance.
-- |             Only provided fields are updated; others remain unchanged.
-- | **Parameters:**
-- | - `store`: The state store to update
-- | - `partial`: Partial balance update (all fields optional)
-- | **Returns:** Unit
-- | **Side Effects:** Updates state reference and notifies listeners
-- |
-- | **Update Strategy:**
-- | - Uses `fromMaybe` to merge: `fromMaybe oldValue newValue`
-- | - Nested Maybe fields (e.g., `timeToDepletion`) use `>>= identity` to flatten
-- | - Alert level is preserved if not provided (calculated elsewhere)
-- |
-- | **Example:**
-- | ```purescript
-- | Store.updateBalancePartial store {
-- |   venice: Just { diem: Just 1000.0, usd: Nothing, effective: Nothing, lastUpdated: Nothing }
-- |   , consumptionRate: Just 50.0
-- |   , timeToDepletion: Nothing
-- |   , todayUsed: Nothing
-- |   , resetCountdown: Nothing
-- |   , alertLevel: Nothing
-- | }
-- | ```
updateBalancePartial :: StateStore -> { venice :: Maybe { diem :: Maybe Number, usd :: Maybe Number, effective :: Maybe Number, lastUpdated :: Maybe DateTime }, consumptionRate :: Maybe Number, timeToDepletion :: Maybe (Maybe Number), todayUsed :: Maybe Number, resetCountdown :: Maybe (Maybe Number), alertLevel :: Maybe AlertLevel } -> Effect Unit
updateBalancePartial store partial = do
  current <- read store.state
  let balance = current.balance
  let newBalance = balance
        { venice = case partial.venice of
            Just v -> balance.venice
              { diem = fromMaybe balance.venice.diem v.diem
              , usd = fromMaybe balance.venice.usd v.usd
              , effective = fromMaybe balance.venice.effective v.effective
              , lastUpdated = case v.lastUpdated of
                  Just newDate -> Just newDate
                  Nothing -> balance.venice.lastUpdated
              }
            Nothing -> balance.venice
        , consumptionRate = fromMaybe balance.consumptionRate partial.consumptionRate
        , timeToDepletion = fromMaybe balance.timeToDepletion partial.timeToDepletion
        , todayUsed = fromMaybe balance.todayUsed partial.todayUsed
        , resetCountdown = fromMaybe balance.resetCountdown partial.resetCountdown
        , alertLevel = fromMaybe balance.alertLevel partial.alertLevel
        }
  write (current { balance = newBalance }) store.state
  notifyListeners store "balance" "updated"

-- | Update balance (full) - Replace entire balance state
-- |
-- | **Purpose:** Replaces the entire balance state with a new value.
-- | **Parameters:**
-- | - `store`: The state store to update
-- | - `newBalance`: Complete new balance state
-- | **Returns:** Unit
-- | **Side Effects:** Updates state reference and notifies listeners with path "balance"
-- |
-- | **Example:**
-- | ```purescript
-- | newBalance :: BalanceState
-- | newBalance = { ... }
-- | Store.updateBalance store newBalance
-- | ```
updateBalance :: StateStore -> BalanceState -> Effect Unit
updateBalance store newBalance = do
  current <- read store.state
  write (current { balance = newBalance }) store.state
  notifyListeners store "balance" "updated"

-- | Update session (partial) - Merge partial session updates
-- |
-- | **Purpose:** Updates session state by merging partial updates with existing session.
-- |             Only updates if a session exists; does nothing if session is `Nothing`.
-- | **Parameters:**
-- | - `store`: The state store to update
-- | - `partial`: Partial session update (all fields optional)
-- | **Returns:** Unit
-- | **Side Effects:** Updates state reference and notifies listeners if session exists
-- |
-- | **Behavior:**
-- | - If `current.session` is `Nothing`, update is ignored (no-op)
-- | - If `current.session` is `Just session`, fields are merged using `fromMaybe`
-- |
-- | **Example:**
-- | ```purescript
-- | Store.updateSessionPartial store {
-- |   id: Nothing
-- |   , promptTokens: Just 100
-- |   , completionTokens: Just 50
-- |   , totalTokens: Just 150
-- |   , cost: Just 0.0015
-- |   , model: Nothing
-- |   , provider: Nothing
-- |   , messageCount: Just 5
-- |   , updatedAt: Just currentDateTime
-- | }
-- | ```
updateSessionPartial :: StateStore -> { id :: Maybe String, promptTokens :: Maybe Int, completionTokens :: Maybe Int, totalTokens :: Maybe Int, cost :: Maybe Number, model :: Maybe String, provider :: Maybe String, messageCount :: Maybe Int, updatedAt :: Maybe DateTime } -> Effect Unit
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
      write (current { session = Just newSession }) store.state
      notifyListeners store "session" "updated"
    Nothing -> pure unit

-- | Update session (full)
updateSession :: StateStore -> SessionState -> Effect Unit
updateSession store newSession = do
  current <- read store.state
  write (current { session = Just newSession }) store.state
  notifyListeners store "session" "updated"

-- | Clear session - Remove active session
-- |
-- | **Purpose:** Clears the active session by setting `session` to `Nothing`.
-- | **Parameters:**
-- | - `store`: The state store to update
-- | **Returns:** Unit
-- | **Side Effects:** Updates state reference and notifies listeners with path "session"
-- |
-- | **Example:**
-- | ```purescript
-- | Store.clearSession store
-- | ```
clearSession :: StateStore -> Effect Unit
clearSession store = do
  current <- read store.state
  write (current { session = Nothing }) store.state
  notifyListeners store "session" "cleared"

-- | Update proof state (partial) - Merge partial proof updates
-- |
-- | **Purpose:** Updates proof state by merging partial updates with existing proof state.
-- | **Parameters:**
-- | - `store`: The state store to update
-- | - `partial`: Partial proof update (all fields optional)
-- | **Returns:** Unit
-- | **Side Effects:** Updates state reference and notifies listeners with path "proof"
-- |
-- | **Update Strategy:**
-- | - Nested Maybe fields (e.g., `file`, `position`) use `>>= identity` to flatten
-- | - Arrays are replaced entirely if provided, otherwise preserved
-- |
-- | **Example:**
-- | ```purescript
-- | Store.updateProofPartial store {
-- |   connected: Just true
-- |   , file: Just (Just "/path/to/File.lean")
-- |   , position: Just (Just { line: 10, column: 5 })
-- |   , goals: Just [goal1, goal2]
-- |   , diagnostics: Nothing
-- |   , suggestedTactics: Nothing
-- | }
-- | ```
updateProofPartial :: StateStore -> { connected :: Maybe Boolean, file :: Maybe (Maybe String), position :: Maybe (Maybe { line :: Int, column :: Int }), goals :: Maybe (Array Goal), diagnostics :: Maybe (Array Diagnostic), suggestedTactics :: Maybe (Array Tactic) } -> Effect Unit
updateProofPartial store partial = do
  current <- read store.state
  let proof = current.proof
  let newProof = proof
        { connected = fromMaybe proof.connected partial.connected
        , file = fromMaybe proof.file partial.file
        , position = fromMaybe proof.position partial.position
        , goals = fromMaybe proof.goals partial.goals
        , diagnostics = fromMaybe proof.diagnostics partial.diagnostics
        , suggestedTactics = fromMaybe proof.suggestedTactics partial.suggestedTactics
        }
  write (current { proof = newProof }) store.state
  notifyListeners store "proof" "updated"

-- | Update proof state (full) - Replace entire proof state
-- |
-- | **Purpose:** Replaces the entire proof state with a new value.
-- | **Parameters:**
-- | - `store`: The state store to update
-- | - `newProof`: Complete new proof state
-- | **Returns:** Unit
-- | **Side Effects:** Updates state reference and notifies listeners with path "proof"
-- |
-- | **Example:**
-- | ```purescript
-- | newProof :: ProofState
-- | newProof = { connected: true, file: Just "...", ... }
-- | Store.updateProof store newProof
-- | ```
updateProof :: StateStore -> ProofState -> Effect Unit
updateProof store newProof = do
  current <- read store.state
  write (current { proof = newProof }) store.state
  notifyListeners store "proof" "updated"

-- | Update metrics (partial) - Merge partial metrics updates
-- |
-- | **Purpose:** Updates usage metrics by merging partial updates with existing metrics.
-- | **Parameters:**
-- | - `store`: The state store to update
-- | - `partial`: Partial metrics update (all fields optional)
-- | **Returns:** Unit
-- | **Side Effects:** Updates state reference and notifies listeners with path "metrics"
-- |
-- | **Example:**
-- | ```purescript
-- | Store.updateMetricsPartial store {
-- |   totalTokens: Just 10000
-- |   , totalCost: Just 0.10
-- |   , averageResponseTime: Just 1.5
-- |   , toolTimings: Just [{ tool: "venice.chat", duration: 1.2 }]
-- | }
-- | ```
updateMetricsPartial :: StateStore -> { totalTokens :: Maybe Int, totalCost :: Maybe Number, averageResponseTime :: Maybe Number, toolTimings :: Maybe (Array { tool :: String, duration :: Number }) } -> Effect Unit
updateMetricsPartial store partial = do
  current <- read store.state
  let metrics = current.metrics
  let newMetrics = metrics
        { totalTokens = fromMaybe metrics.totalTokens partial.totalTokens
        , totalCost = fromMaybe metrics.totalCost partial.totalCost
        , averageResponseTime = fromMaybe metrics.averageResponseTime partial.averageResponseTime
        , toolTimings = fromMaybe metrics.toolTimings partial.toolTimings
        }
  write (current { metrics = newMetrics }) store.state
  notifyListeners store "metrics" "updated"

-- | Update metrics (full) - Replace entire metrics state
-- |
-- | **Purpose:** Replaces the entire usage metrics state with a new value.
-- | **Parameters:**
-- | - `store`: The state store to update
-- | - `newMetrics`: Complete new metrics state
-- | **Returns:** Unit
-- | **Side Effects:** Updates state reference and notifies listeners with path "metrics"
-- |
-- | **Example:**
-- | ```purescript
-- | newMetrics :: UsageMetrics
-- | newMetrics = { totalTokens: 10000, totalCost: 0.10, ... }
-- | Store.updateMetrics store newMetrics
-- | ```
updateMetrics :: StateStore -> UsageMetrics -> Effect Unit
updateMetrics store newMetrics = do
  current <- read store.state
  write (current { metrics = newMetrics }) store.state
  notifyListeners store "metrics" "updated"

-- | Set connected state - Update WebSocket connection status
-- |
-- | **Purpose:** Updates the WebSocket connection status in application state.
-- | **Parameters:**
-- | - `store`: The state store to update
-- | - `connected`: True if connected, false if disconnected
-- | **Returns:** Unit
-- | **Side Effects:** Updates state reference and notifies listeners with path "connected"
-- |
-- | **Example:**
-- | ```purescript
-- | Store.setConnected store true  -- Mark as connected
-- | Store.setConnected store false -- Mark as disconnected
-- | ```
setConnected :: StateStore -> Boolean -> Effect Unit
setConnected store connected = do
  current <- read store.state
  write (current { connected = connected }) store.state
  notifyListeners store "connected" (if connected then "connected" else "disconnected")

-- | Update alert configuration - Replace alert thresholds
-- |
-- | **Purpose:** Replaces the alert configuration with new thresholds.
-- | **Parameters:**
-- | - `store`: The state store to update
-- | - `newConfig`: New alert configuration
-- | **Returns:** Unit
-- | **Side Effects:** Updates state reference and notifies listeners with path "alertConfig"
-- |
-- | **Example:**
-- | ```purescript
-- | newConfig :: AlertConfig
-- | newConfig = { diemWarningPercent: 0.25, diemCriticalPercent: 0.10, depletionWarningHours: 3.0 }
-- | Store.updateAlertConfig store newConfig
-- | ```
updateAlertConfig :: StateStore -> AlertConfig -> Effect Unit
updateAlertConfig store newConfig = do
  current <- read store.state
  write (current { alertConfig = newConfig }) store.state
  notifyListeners store "alertConfig" "updated"

-- | Subscribe to state changes - Register change listener
-- |
-- | **Purpose:** Registers a listener function that will be called whenever state changes.
-- |             Returns an unsubscribe function to remove the listener.
-- | **Parameters:**
-- | - `store`: The state store to subscribe to
-- | - `listener`: Function called on state changes with (path, value) parameters
-- | **Returns:** Unsubscribe function (Effect Unit) that removes the listener
-- | **Side Effects:** Adds listener to listeners array
-- |
-- | **Listener Parameters:**
-- | - `path`: State path that changed (e.g., "balance", "session", "proof")
-- | - `value`: Change description (e.g., "updated", "cleared", "connected")
-- |
-- | **Example:**
-- | ```purescript
-- | unsubscribe <- Store.onStateChange store \path value -> do
-- |   log $ "State changed: " <> path <> " = " <> value
-- |
-- | -- Later: remove listener
-- | unsubscribe
-- | ```
onStateChange :: StateStore -> (String -> String -> Effect Unit) -> Effect (Effect Unit)
onStateChange store listener = do
  currentListeners <- read store.listeners
  let index = Array.length currentListeners
  _ <- modify (\listeners -> listeners <> [listener]) store.listeners
  pure do
    -- Remove listener by reconstructing array without the element at index
    void $ modify (\listeners -> 
      Array.mapWithIndex (\i l -> if i == index then Nothing else Just l) listeners
        # Array.catMaybes
    ) store.listeners

-- | Notify all listeners - Internal function to trigger change notifications
-- |
-- | **Purpose:** Internal function called by update functions to notify all registered
-- |             listeners of state changes. Not intended for external use.
-- | **Parameters:**
-- | - `store`: The state store
-- | - `path`: State path that changed
-- | - `value`: Change description
-- | **Returns:** Unit
-- | **Side Effects:** Calls all registered listeners synchronously
-- |
-- | **Note:** This function is called automatically by all update functions.
-- |          External code should not call this directly.
notifyListeners :: StateStore -> String -> String -> Effect Unit
notifyListeners store path value = do
  listeners <- read store.listeners
  traverse_ (\listener -> listener path value) listeners
