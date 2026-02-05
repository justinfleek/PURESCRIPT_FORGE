-- | Pure State Reducer - Predictable State Transitions with Undo/Redo
-- |
-- | **What:** Provides pure functions for state transitions in the sidepanel application,
-- |         with automatic undo/redo history tracking. All state changes go through this
-- |         reducer, ensuring predictable and reversible state updates.
-- | **Why:** Implements the reducer pattern for predictable state management. Undo/redo
-- |         functionality is built-in, allowing users to revert state changes. Pure
-- |         functions ensure testability and prevent side effects in state updates.
-- | **How:** Uses a two-level reducer pattern:
-- |         - `reduce`: Top-level reducer that handles undo/redo and history tracking
-- |         - `reduceWithoutHistory`: Internal reducer that applies state transitions
-- |         All actions (except Undo/Redo) push new state to history. Undo/Redo restore
-- |         from history without adding new entries.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.AppState`: Application state type
-- | - `Sidepanel.State.Actions`: Action type definitions
-- | - `Sidepanel.State.UndoRedo`: Undo/redo history management
-- | - `Sidepanel.State.Balance`: Balance state calculations
-- |
-- | **Mathematical Foundation:**
-- | - **Reducer Invariant:** For any state `s` and action `a`, `reduce s a` returns a
-- |   valid AppState. No invalid states are possible.
-- | - **History Invariant:** Undo/Redo operations preserve history structure. Undo removes
-- |   current state from history, Redo restores it. History never grows unbounded (bounded
-- |   by UndoRedo implementation).
-- | - **Idempotency:** Applying the same action twice may produce different results if
-- |   state-dependent (e.g., incrementing counters). Actions are not required to be idempotent.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.State.Reducer as Reducer
-- | import Sidepanel.State.Actions as Actions
-- |
-- | -- Apply action to state
-- | newState = Reducer.reduce currentState (Actions.BalanceUpdated update)
-- |
-- | -- Undo last action
-- | undoneState = Reducer.reduce newState Actions.Undo
-- |
-- | -- Redo undone action
-- | redoneState = Reducer.reduce undoneState Actions.Redo
-- | ```
-- |
-- | Based on spec 41-STATE-MANAGEMENT.md
module Sidepanel.State.Reducer where

import Prelude
import Data.Array as Array
import Data.DateTime (DateTime(..))
import Data.Date (Date, canonicalDate)
import Data.Time (Time, midnight)
import Data.Date.Component (Year(..), Month(..), Day(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Sidepanel.State.AppState (AppState, SessionState, AlertLevel(..), Panel, Theme, Alert, Message)
import Sidepanel.State.Balance (BalanceState, VeniceBalance, FlkBalance, TokenUsage, calculateAlertLevel, BalanceSnapshot)
import Sidepanel.State.Actions (Action(..), BalanceUpdate, SessionUpdate, UsageRecord, AlertData, SessionMetadataUpdate)
import Sidepanel.State.UndoRedo as UndoRedo
import Sidepanel.State.BalanceMetrics as BalanceMetrics
import Sidepanel.State.Sessions as Sessions
import Sidepanel.FFI.DateTime (getCurrentDateTime, toTimestamp)
import Data.Map as Map

-- | Pure state reducer with automatic history tracking
-- |
-- | **Purpose:** Main reducer function that applies actions to state and manages undo/redo
-- |             history. Undo/Redo actions restore from history, all other actions push new
-- |             state to history.
-- | **Parameters:**
-- | - `state`: Current application state
-- | - `action`: Action to apply
-- | **Returns:** New application state after applying action
-- | **Side Effects:** None (pure function)
-- |
-- | **Behavior:**
-- | - `Undo`: Restores previous state from history (if available)
-- | - `Redo`: Restores next state from history (if available)
-- | - All other actions: Applies state transition and pushes new state to history
-- |
-- | **History Management:**
-- | - Undo/Redo operations update `undoRedo` state but don't add new history entries
-- | - All other actions add new history entry via `UndoRedo.pushState`
-- |
-- | **Example:**
-- | ```purescript
-- | newState = reduce currentState (BalanceUpdated update)
-- | undoneState = reduce newState Undo
-- | redoneState = reduce undoneState Redo
-- | ```
reduce :: AppState -> Action -> AppState
reduce state action = case action of
  Undo ->
    case UndoRedo.undo state.undoRedo of
      Just newUndoRedo -> case UndoRedo.getState newUndoRedo of
        Just restoredState -> restoredState { undoRedo = newUndoRedo }
        Nothing -> state  -- Should not happen, but preserve state if it does
      Nothing -> state  -- Cannot undo, preserve current state
  
  Redo ->
    case UndoRedo.redo state.undoRedo of
      Just newUndoRedo -> case UndoRedo.getState newUndoRedo of
        Just restoredState -> restoredState { undoRedo = newUndoRedo }
        Nothing -> state  -- Should not happen, but preserve state if it does
      Nothing -> state  -- Cannot redo, preserve current state
  
  -- All other actions: apply reducer and track in history
  _ ->
    let
      newState = reduceWithoutHistory state action
      -- Push new state to history
      updatedUndoRedo = UndoRedo.pushState newState state.undoRedo
    in
      newState { undoRedo = updatedUndoRedo }

-- | Internal reducer that doesn't track history (used by reduce)
-- |
-- | **Purpose:** Applies state transitions without history tracking. Used internally by
-- |             `reduce` to compute new state before adding to history. Handles all action
-- |             types except Undo/Redo (which are handled in `reduce`).
-- | **Parameters:**
-- | - `state`: Current application state
-- | - `action`: Action to apply (must not be Undo or Redo)
-- | **Returns:** New application state after applying action
-- | **Side Effects:** None (pure function)
-- |
-- | **Action Handlers:**
-- | - `Connected`/`Disconnected`: Update connection status
-- | - `BalanceUpdated`: Merge balance update with existing balance
-- | - `SessionUpdated`/`SessionCleared`: Update or clear session
-- | - `UsageRecorded`: Add usage to current session
-- | - `GoalsUpdated`/`DiagnosticsUpdated`/`TacticsUpdated`: Update proof state
-- | - `ProofConnected`/`ProofDisconnected`: Update proof connection status
-- | - `SnapshotCreated`/`SnapshotSelected`/`SnapshotRestored`: Manage snapshots
-- | - `ToggleSidebar`/`SetActivePanel`/`SetTheme`: Update UI state
-- | - `AlertTriggered`/`DismissAlert`: Manage alerts
-- |
-- | **Note:** Undo and Redo cases return state unchanged (should not reach here).
reduceWithoutHistory :: AppState -> Action -> AppState
reduceWithoutHistory state = case _ of
  Connected ->
    state { connected = true }
  
  Disconnected ->
    state { connected = false }
  
  PingReceived timestamp ->
    state { lastSyncTime = Just timestamp }
  
  BalanceUpdated update ->
    let
      -- Use timestamp from update, or fall back to lastUpdated, or use current time approximation
      currentTime = case update.timestamp of
        Just ts -> ts
        Nothing -> case state.balance.lastUpdated of
          Just dt -> dt
          Nothing -> DateTime (canonicalDate (Year 2026) (Month 1) (Day 1)) midnight  -- Fallback
    in
      state { balance = updateBalance state.balance update currentTime }
  
  CountdownTick ->
    state { balance = tickCountdown state.balance }
  
  AlertLevelChanged level ->
    -- Alert level is calculated, not set directly
    state { balance = state.balance { alertLevel = calculateAlertLevel state.balance } }
  
  RateLimitUpdated headers ->
    let
      -- Get current time for update
      currentTime = case state.rateLimit.lastUpdated of
        Just dt -> dt
        Nothing -> DateTime (canonicalDate (Year 2026) (Month 1) (Day 1)) midnight  -- Fallback, would use getCurrentDateTime in real app
    in
      state { rateLimit = updateFromHeaders state.rateLimit headers currentTime }
  
  RateLimitHit retryAfterSeconds ->
    -- Apply exponential backoff (recentLimitCount would come from state tracking)
    let
      recentLimitCount = 0  -- Would track this in state
      updated = applyBackoff state.rateLimit retryAfterSeconds recentLimitCount
    in
      state { rateLimit = updated }
  
  RateLimitBackoffTick ->
    -- Decrement backoff timer by 1 second (1000ms)
    let
      newBackoff = if state.rateLimit.backoffMs > 1000.0
        then state.rateLimit.backoffMs - 1000.0
        else 0.0
    in
      state { rateLimit = state.rateLimit { backoffMs = newBackoff } }
  
  SessionUpdated session ->
    case state.session of
      Nothing -> 
        -- New session - use startedAt from update
        -- Note: Component should provide startedAt, but we fallback if missing
        state { session = Just $ createSessionFromUpdate session Nothing }
      Just existing ->
        state { session = Just $ updateSessionFromExisting existing session }
  
  SessionCleared ->
    state { session = Nothing, messages = [] }
  
  MessageAdded message ->
    state { messages = Array.snoc state.messages message }
  
  MessagesCleared ->
    state { messages = [] }
  
  -- Multi-Session Management Actions
  SessionOpened sessionId title icon ->
    let
      updatedTabs = Sessions.openTab state.sessionTabs sessionId title icon
    in
      state
        { sessionTabs = updatedTabs
        , activeSessionId = Just sessionId
        }
  
  SessionClosed sessionId ->
    let
      updatedTabs = Sessions.closeTab state.sessionTabs sessionId
      -- Remove session from sessions Map
      updatedSessions = Map.delete sessionId state.sessions
      -- Remove metadata
      updatedMetadata = Map.delete sessionId state.sessionMetadata
      -- Remove messages
      updatedSessionMessages = Map.delete sessionId state.sessionMessages
      -- If closed session was active, update activeSessionId
      newActiveSessionId = if state.activeSessionId == Just sessionId
        then updatedTabs.activeTabId
        else state.activeSessionId
    in
      state
        { sessionTabs = updatedTabs
        , sessions = updatedSessions
        , sessionMetadata = updatedMetadata
        , sessionMessages = updatedSessionMessages
        , activeSessionId = newActiveSessionId
        }
  
  SessionSwitched sessionId ->
    let
      updatedTabs = Sessions.switchToTab state.sessionTabs sessionId
    in
      state
        { sessionTabs = updatedTabs
        , activeSessionId = Just sessionId
        }
  
  TabsReordered newOrder ->
    let
      updatedTabs = Sessions.reorderTabs state.sessionTabs newOrder
    in
      state { sessionTabs = updatedTabs }
  
  TabPinned sessionId ->
    let
      updatedTabs = Sessions.pinTab state.sessionTabs sessionId
    in
      state { sessionTabs = updatedTabs }
  
  TabUnpinned sessionId ->
    let
      updatedTabs = Sessions.unpinTab state.sessionTabs sessionId
    in
      state { sessionTabs = updatedTabs }
  
  TabRenamed sessionId newTitle ->
    let
      updatedTabs = Sessions.renameTab state.sessionTabs sessionId newTitle
    in
      state { sessionTabs = updatedTabs }
  
  TabIconSet sessionId newIcon ->
    let
      updatedTabs = Sessions.setTabIcon state.sessionTabs sessionId newIcon
    in
      state { sessionTabs = updatedTabs }
  
  SessionCreated sessionUpdate title icon ->
    let
      -- Create session state
      newSession = createSessionFromUpdate sessionUpdate Nothing
      -- Create metadata
      newMetadata =
        { title: title
        , icon: icon
        , color: Nothing
        , status: Sessions.Active
        , parentId: Nothing
        , branchPoint: Nothing
        , children: []
        }
      -- Add to sessions Map
      updatedSessions = Map.insert sessionUpdate.id newSession state.sessions
      -- Add to metadata Map
      updatedMetadata = Map.insert sessionUpdate.id newMetadata state.sessionMetadata
      -- Initialize empty messages array
      updatedSessionMessages = Map.insert sessionUpdate.id [] state.sessionMessages
      -- Open tab
      updatedTabs = Sessions.openTab state.sessionTabs sessionUpdate.id title icon
    in
      state
        { sessions = updatedSessions
        , sessionMetadata = updatedMetadata
        , sessionMessages = updatedSessionMessages
        , sessionTabs = updatedTabs
        , activeSessionId = Just sessionUpdate.id
        }
  
  SessionBranchCreated parentSessionId messageIndex description branchSessionId branchTitle ->
    let
      -- Get parent session
      parentSession = Map.lookup parentSessionId state.sessions
      parentMetadata = Map.lookup parentSessionId state.sessionMetadata
      parentMessages = Map.lookup parentSessionId state.sessionMessages
      
      -- Create branch session (copy parent's session state, reset tokens/cost)
      branchSession = case parentSession of
        Just parent ->
          { id: branchSessionId
          , model: parent.model
          , promptTokens: 0
          , completionTokens: 0
          , totalTokens: 0
          , cost: 0.0
          , messageCount: messageIndex + 1  -- Messages up to branch point
          , startedAt: parent.startedAt
          }
        Nothing ->
          -- Fallback if parent not found
          { id: branchSessionId
          , model: "gpt-4"
          , promptTokens: 0
          , completionTokens: 0
          , totalTokens: 0
          , cost: 0.0
          , messageCount: 0
          , startedAt: DateTime (canonicalDate (Year 2026) (Month 1) (Day 1)) midnight
          }
      
      -- Create branch metadata
      branchMetadata =
        { title: branchTitle
        , icon: "🔀"
        , color: Nothing
        , status: Sessions.Active
        , parentId: Just parentSessionId
        , branchPoint: Just messageIndex
        , children: []
        }
      
      -- Copy messages up to branch point
      branchMessages = case parentMessages of
        Just msgs -> Array.take (messageIndex + 1) msgs
        Nothing -> []
      
      -- Update parent's children list
      updatedParentMetadata = case parentMetadata of
        Just meta ->
          Map.insert parentSessionId (meta { children = Array.snoc meta.children branchSessionId }) state.sessionMetadata
        Nothing ->
          state.sessionMetadata
      
      -- Add branch to sessions
      updatedSessions = Map.insert branchSessionId branchSession state.sessions
      -- Add branch metadata
      updatedMetadata = Map.insert branchSessionId branchMetadata updatedParentMetadata
      -- Add branch messages
      updatedSessionMessages = Map.insert branchSessionId branchMessages state.sessionMessages
      -- Open branch tab
      updatedTabs = Sessions.openTab state.sessionTabs branchSessionId branchTitle "🔀"
    in
      state
        { sessions = updatedSessions
        , sessionMetadata = updatedMetadata
        , sessionMessages = updatedSessionMessages
        , sessionTabs = updatedTabs
        , activeSessionId = Just branchSessionId
        }
  
  SessionBranchMerged sourceSessionId targetSessionId ->
    let
      -- Get source messages (after branch point)
      sourceMessages = Map.lookup sourceSessionId state.sessionMessages
      sourceMetadata = Map.lookup sourceSessionId state.sessionMetadata
      targetMessages = Map.lookup targetSessionId state.sessionMessages
      
      -- Determine branch point
      branchPoint = case sourceMetadata of
        Just meta -> meta.branchPoint
        Nothing -> Nothing
      
      -- Get messages after branch point from source
      messagesToMerge = case branchPoint, sourceMessages of
        Just idx, Just msgs -> Array.drop (idx + 1) msgs
        _, Just msgs -> msgs  -- If no branch point, merge all
        _, Nothing -> []
      
      -- Append to target messages
      updatedTargetMessages = case targetMessages of
        Just msgs -> Array.append msgs messagesToMerge
        Nothing -> messagesToMerge
      
      -- Update target session messages
      updatedSessionMessages = Map.insert targetSessionId updatedTargetMessages state.sessionMessages
      
      -- Archive source session (update metadata status)
      updatedSourceMetadata = case sourceMetadata of
        Just meta -> Map.insert sourceSessionId (meta { status = Sessions.Archived }) state.sessionMetadata
        Nothing -> state.sessionMetadata
    in
      state
        { sessionMessages = updatedSessionMessages
        , sessionMetadata = updatedSourceMetadata
        }
  
  MessageAddedToSession sessionId message ->
    let
      -- Get existing messages for session
      existingMessages = Map.lookup sessionId state.sessionMessages
      updatedMessages = case existingMessages of
        Just msgs -> Array.snoc msgs message
        Nothing -> [message]
      
      -- Update session messages Map
      updatedSessionMessages = Map.insert sessionId updatedMessages state.sessionMessages
      
      -- Also update legacy messages array if this is the active session
      legacyMessages = if state.activeSessionId == Just sessionId
        then updatedMessages
        else state.messages
    in
      state
        { sessionMessages = updatedSessionMessages
        , messages = legacyMessages  -- Keep legacy field in sync for compatibility
        }
  
  MessagesClearedForSession sessionId ->
    let
      -- Clear messages for session
      updatedSessionMessages = Map.insert sessionId [] state.sessionMessages
      
      -- Also clear legacy messages if this is the active session
      legacyMessages = if state.activeSessionId == Just sessionId
        then []
        else state.messages
    in
      state
        { sessionMessages = updatedSessionMessages
        , messages = legacyMessages  -- Keep legacy field in sync for compatibility
        }
  
  SessionMetadataUpdated sessionId update ->
    let
      -- Get existing metadata
      existingMetadata = Map.lookup sessionId state.sessionMetadata
      
      -- Apply partial update
      updatedMetadata = case existingMetadata of
        Just meta ->
          Map.insert sessionId
            { title: case update.title of
                Just t -> t
                Nothing -> meta.title
            , icon: case update.icon of
                Just i -> i
                Nothing -> meta.icon
            , color: case update.color of
                Just c -> c
                Nothing -> meta.color
            , status: case update.status of
                Just s -> s
                Nothing -> meta.status
            , parentId: case update.parentId of
                Just p -> p
                Nothing -> meta.parentId
            , branchPoint: case update.branchPoint of
                Just bp -> bp
                Nothing -> meta.branchPoint
            , children: case update.children of
                Just ch -> ch
                Nothing -> meta.children
            }
            state.sessionMetadata
        Nothing ->
          -- Create new metadata if doesn't exist
          Map.insert sessionId
            { title: case update.title of
                Just t -> t
                Nothing -> "New Session"
            , icon: case update.icon of
                Just i -> i
                Nothing -> "💬"
            , color: case update.color of
                Just c -> c
                Nothing -> Nothing
            , status: case update.status of
                Just s -> s
                Nothing -> Sessions.Active
            , parentId: case update.parentId of
                Just p -> p
                Nothing -> Nothing
            , branchPoint: case update.branchPoint of
                Just bp -> bp
                Nothing -> Nothing
            , children: case update.children of
                Just ch -> ch
                Nothing -> []
            }
            state.sessionMetadata
    in
      state { sessionMetadata = updatedMetadata }
  
  UsageRecorded usage ->
    -- Update active session if exists
    case state.activeSessionId of
      Just sessionId ->
        case Map.lookup sessionId state.sessions of
          Just s ->
            let
              updatedSession = s
                { promptTokens = s.promptTokens + usage.prompt
                , completionTokens = s.completionTokens + usage.completion
                , totalTokens = s.totalTokens + usage.prompt + usage.completion
                , cost = s.cost + usage.cost
                }
              updatedSessions = Map.insert sessionId updatedSession state.sessions
              -- Also update legacy session field if active
              legacySession = Just updatedSession
            in
              state
                { sessions = updatedSessions
                , session = legacySession  -- Keep legacy field in sync
                }
          Nothing -> state
      Nothing ->
        -- Fallback to legacy session
        case state.session of
          Nothing -> state
          Just s -> state 
            { session = Just $ s
                { promptTokens = s.promptTokens + usage.prompt
                , completionTokens = s.completionTokens + usage.completion
                , totalTokens = s.totalTokens + usage.prompt + usage.completion
                , cost = s.cost + usage.cost
                }
            }
  
  GoalsUpdated goals ->
    state { proof = state.proof { goals = goals } }
  
  DiagnosticsUpdated diagnostics ->
    state { proof = state.proof { diagnostics = diagnostics } }
  
  TacticsUpdated tactics ->
    state { proof = state.proof { suggestedTactics = tactics } }
  
  ProofConnected ->
    state { proof = state.proof { connected = true } }
  
  ProofDisconnected ->
    state { proof = state.proof { connected = false } }
  
  SnapshotCreated snapshot ->
    state { snapshots = Array.snoc state.snapshots snapshot }
  
  SnapshotSelected id ->
    state { selectedSnapshotId = Just id }
  
  SnapshotRestored _ ->
    state -- Restore logic handled elsewhere
  
  ToggleSidebar ->
    state { ui = state.ui { sidebarCollapsed = not state.ui.sidebarCollapsed } }
  
  SetActivePanel panel ->
    state { ui = state.ui { activePanel = panel } }
  
  SetTheme theme ->
    state { ui = state.ui { theme = theme } }
  
  AlertTriggered alert ->
    let alertId = "alert-" <> show (Array.length state.ui.alerts)
    in state { ui = state.ui { alerts = Array.snoc state.ui.alerts $ toAlert alert alertId } }
  
  DismissAlert id ->
    state { ui = state.ui { alerts = Array.filter (\a -> a.id /= id) state.ui.alerts } }
  
  -- Undo and Redo should not reach here
  -- They are handled in the reduce function
  Undo -> state
  Redo -> state

-- | Update balance state (supports all providers)
-- |
-- | **Purpose:** Merges balance update with existing balance state, supporting multiple
-- |             providers (currently Venice). Creates Venice balance if update contains
-- |             Diem data and no balance exists.
-- | **Parameters:**
-- | - `balance`: Current balance state
-- | - `update`: Balance update to apply
-- | **Returns:** Updated balance state
-- | **Side Effects:** None (pure function)
-- |
-- | **Update Strategy:**
-- | - If Venice balance exists: Merge update fields
-- | - If no Venice balance and update has Diem data: Create new Venice balance
-- | - Alert level is recalculated from balance thresholds
-- | - Cost is derived from Venice USD balance if available
-- |
-- | **Example:**
-- | ```purescript
-- | update :: BalanceUpdate
-- | update = { diem: 1000.0, usd: 10.0, effective: 1000.0, ... }
-- | newBalance = updateBalance currentBalance update
-- | ```
updateBalance :: BalanceState -> BalanceUpdate -> DateTime -> BalanceState
updateBalance balance update currentTime =
  let
    -- Update Venice balance if Venice data provided
    updatedVenice = case update.diem, update.usd of
      Just diem, Just usd ->
        case balance.venice of
          Just venice ->
            Just venice
              { diem = diem
              , usd = usd
              , effective = update.effective
              , todayUsed = update.todayUsed
              }
          Nothing ->
            -- Create Venice balance if update has Diem/USD data
            Just
              { diem: diem
              , usd: usd
              , effective: update.effective
              , todayUsed: update.todayUsed
              , todayStartBalance: update.todayUsed + diem
              , resetCountdown: Nothing  -- Would calculate from current time
              }
      _, _ -> balance.venice  -- No Venice update, preserve existing
    
    -- Update FLK balance if FLK data provided
    updatedFlk = case update.flk of
      Just flk ->
        case balance.flk of
          Just flkBalance ->
            Just flkBalance
              { flk = flk
              , effective = update.effective
              , todayUsed = update.todayUsed
              }
          Nothing ->
            -- Create FLK balance if update has FLK data
            Just
              { flk: flk
              , effective: update.effective
              , todayUsed: update.todayUsed
              , todayStartBalance: update.todayUsed + flk
              }
      Nothing -> balance.flk  -- No FLK update, preserve existing
    
    -- Add snapshot to history (if Venice balance updated)
    newSnapshot = case updatedVenice of
      Just venice ->
        Just { timestamp: currentTime, diem: venice.diem, usd: venice.usd }
      Nothing -> Nothing
    
    -- Update history: add new snapshot, keep last 24 hours
    currentTimestamp = toTimestamp currentTime
    oneDayAgo = currentTimestamp - (24.0 * 60.0 * 60.0 * 1000.0)
    filteredHistory = Array.filter (\s -> toTimestamp s.timestamp > oneDayAgo) balance.balanceHistory
    updatedHistory = case newSnapshot of
      Just snapshot -> Array.snoc filteredHistory snapshot
      Nothing -> filteredHistory
    
    -- Calculate consumption rate from history (prefer client-side calculation)
    consumptionRate = if Array.length updatedHistory >= 2 then
        BalanceMetrics.calculateConsumptionRate updatedHistory currentTime
      else
        update.consumptionRate  -- Fallback to server-provided rate if insufficient history
    
    -- Calculate time to depletion from current balance and rate
    currentDiem = case updatedVenice of
      Just venice -> venice.diem
      Nothing -> 0.0
    timeToDepletion = BalanceMetrics.calculateTimeToDepletion currentDiem consumptionRate
    
    -- Update balance with calculated metrics
    updatedBalance = balance
      { venice = updatedVenice
      , flk = updatedFlk
      , balanceHistory = updatedHistory
      , consumptionRate = consumptionRate
      , timeToDepletion = timeToDepletion
      , todayCost = case updatedVenice of
          Just venice -> venice.usd  -- Use USD balance as proxy for cost
          Nothing -> balance.todayCost  -- Preserve existing cost if no Venice balance
      , lastUpdated = Just currentTime
      }
  in
    updatedBalance { alertLevel = calculateAlertLevel updatedBalance }

-- | Tick countdown timer - Decrement depletion countdown
-- |
-- | **Purpose:** Decrements `timeToDepletion` by 1 second (1/3600 hours) to provide
-- |             smooth countdown animation between server updates. Server provides
-- |             accurate calculations via BalanceUpdate.
-- | **Parameters:**
-- | - `balance`: Current balance state
-- | **Returns:** Updated balance state with decremented countdown
-- | **Side Effects:** None (pure function)
-- |
-- | **Behavior:**
-- | - If `timeToDepletion` is `Just hours`: Decrement by 1/3600 hours
-- | - If result <= 0: Set to `Nothing`
-- | - If `timeToDepletion` is `Nothing`: Leave unchanged
-- |
-- | **Example:**
-- | ```purescript
-- | -- Called every second for countdown animation
-- | updatedBalance = tickCountdown currentBalance
-- | ```
tickCountdown :: BalanceState -> BalanceState
tickCountdown balance = balance
  { timeToDepletion = case balance.timeToDepletion of
      Just hours ->
        -- Decrement by 1 second, which is 1/3600 hours
        let newHours = hours - (1.0 / 3600.0)
        in if newHours <= 0.0 then Nothing else Just newHours
      Nothing -> Nothing
  }

-- | Update session state (preserves startedAt from existing session)
-- |
-- | **Purpose:** Updates an existing session with new data, preserving the `startedAt`
-- |             timestamp from the original session.
-- | **Parameters:**
-- | - `existing`: Current session state
-- | - `update`: Session update data
-- | **Returns:** Updated session state
-- | **Side Effects:** None (pure function)
-- |
-- | **Preservation:**
-- | - `startedAt` is always preserved from `existing` session
-- | - All other fields come from `update`
-- |
-- | **Example:**
-- | ```purescript
-- | updatedSession = updateSessionFromExisting currentSession update
-- | ```
updateSessionFromExisting :: SessionState -> SessionUpdate -> SessionState
updateSessionFromExisting existing update =
  { id: update.id
  , model: update.model
  , promptTokens: update.promptTokens
  , completionTokens: update.completionTokens
  , totalTokens: update.totalTokens
  , cost: update.cost
  , messageCount: update.messageCount
  , startedAt: existing.startedAt
  }

-- | Create new session from update - Initialize new session
-- |
-- | **Purpose:** Creates a new session state from an update, handling `startedAt` timestamp.
-- |             If `update.startedAt` is `Nothing`, uses `maybeStartedAt` parameter.
-- | **Parameters:**
-- | - `update`: Session update data
-- | - `maybeStartedAt`: Fallback DateTime if update doesn't provide startedAt
-- | **Returns:** New session state
-- | **Side Effects:** None (pure function)
-- |
-- | **Timestamp Resolution:**
-- | 1. Use `update.startedAt` if provided
-- | 2. Otherwise use `maybeStartedAt` if provided
-- | 3. Otherwise use epoch (1970-01-01) as sentinel value
-- |
-- | **Note:** Caller should always provide `maybeStartedAt` with current DateTime if
-- |          `update.startedAt` is `Nothing`. Epoch sentinel is a fallback that components
-- |          can detect and replace.
-- |
-- | **Example:**
-- | ```purescript
-- | now <- getCurrentDateTime
-- | newSession = createSessionFromUpdate update (Just now)
-- | ```
createSessionFromUpdate :: SessionUpdate -> Maybe DateTime -> SessionState
createSessionFromUpdate update maybeStartedAt =
  { id: update.id
  , model: update.model
  , promptTokens: update.promptTokens
  , completionTokens: update.completionTokens
  , totalTokens: update.totalTokens
  , cost: update.cost
  , messageCount: update.messageCount
  , startedAt: case update.startedAt of
      Just dt -> dt
      Nothing -> case maybeStartedAt of
        Just dt -> dt
        -- Fallback: This should never happen - caller must provide DateTime
        -- In production, this would throw an error or use Effect to get current time
        -- For now, we use a sentinel value (epoch) that components can detect and replace
        -- This is a compromise to keep reducer pure while avoiding unsafeCoerce
        -- Better solution: Make startedAt non-optional in SessionUpdate
        Nothing -> 
          let
            defaultDate = canonicalDate (Year 1970) (Month bottom) (Day 1)
            defaultTime = midnight
          in DateTime defaultDate defaultTime
  }

-- | Convert alert data to alert - Create Alert from AlertData
-- |
-- | **Purpose:** Converts AlertData (from action) to Alert (for UI state), adding a
-- |             unique ID.
-- | **Parameters:**
-- | - `alert`: Alert data from action
-- | - `id`: Unique alert ID (typically generated from alert count)
-- | **Returns:** Alert type for UI state
-- | **Side Effects:** None (pure function)
-- |
-- | **Example:**
-- | ```purescript
-- | alertId = "alert-" <> show alertCount
-- | alert = toAlert alertData alertId
-- | ```
toAlert :: AlertData -> String -> Alert
toAlert alert id =
  { id: id
  , level: alert.level
  , message: alert.message
  , timestamp: alert.timestamp
  }
