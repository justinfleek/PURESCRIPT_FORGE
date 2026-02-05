# 41-STATE-MANAGEMENT: Centralized State Store

## Overview

The frontend uses a centralized state store pattern, similar to Redux but leveraging PureScript's type system for compile-time guarantees. All state flows through a single store, making the application predictable and debuggable.

---

## Architecture

### Unidirectional Data Flow

```
                    ┌─────────────────────────────────┐
                    │           STATE STORE           │
                    │                                 │
   WebSocket ──────►│  ┌─────────┐    ┌───────────┐ │
   Messages         │  │ State   │───►│ Selectors │─┼───► Components
                    │  └─────────┘    └───────────┘ │         │
                    │       ▲                        │         │
                    │       │                        │         │
                    │  ┌─────────┐                   │         │
   User Actions ◄───┼──│ Reducer │◄──────────────────┼─────────┘
                    │  └─────────┘                   │    Actions
                    │                                 │
                    └─────────────────────────────────┘
```

### Core Principles

1. **Single source of truth** - All state in one place
2. **State is read-only** - Changed only through actions
3. **Pure reducers** - State transitions are pure functions
4. **Typed actions** - ADT ensures exhaustive handling

---

## State Definition

### AppState Type

```purescript
module Sidepanel.State.AppState where

import Prelude
import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Data.Map (Map)
import Data.Set (Set)

-- Root state type
type AppState =
  { -- Connection
    connected :: Boolean
  , lastSyncTime :: Maybe DateTime
  
  -- Balance
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
  }

-- Balance state slice
type BalanceState =
  { diem :: Number
  , usd :: Number
  , effective :: Number
  , lastUpdated :: Maybe DateTime
  , alertLevel :: AlertLevel
  , metrics :: BalanceMetrics
  }

type BalanceMetrics =
  { consumptionRate :: Number      -- Per hour
  , timeToDepletion :: Maybe Number -- Hours
  , todayUsed :: Number
  , todayStartBalance :: Number
  }

data AlertLevel = Normal | Warning | Critical | Depleted

-- Session state slice
type SessionState =
  { id :: String
  , model :: String
  , provider :: String
  , startedAt :: DateTime
  , promptTokens :: Int
  , completionTokens :: Int
  , cost :: Number
  , messages :: Array Message
  , isStreaming :: Boolean
  }

-- Proof state slice
type ProofState =
  { connected :: Boolean
  , currentFile :: Maybe String
  , goals :: Array ProofGoal
  , diagnostics :: Array Diagnostic
  , suggestions :: Array TacticSuggestion
  }

-- UI state slice
type UIState =
  { currentRoute :: Route
  , sidebarCollapsed :: Boolean
  , commandPaletteOpen :: Boolean
  , selectedTimeRange :: TimeRange
  , expandedMessages :: Set String
  , notifications :: Array Notification
  }

-- Settings
type Settings =
  { theme :: Theme
  , alertThresholds :: AlertThresholds
  , keyboardEnabled :: Boolean
  , vimMode :: Boolean
  , features :: FeatureFlags
  }
```

---

## Actions

### Action ADT

```purescript
module Sidepanel.State.Actions where

import Prelude
import Data.DateTime (DateTime)
import Sidepanel.State.AppState

-- All possible state changes
data Action
  -- Connection
  = SetConnected Boolean
  | SetLastSyncTime DateTime
  
  -- Balance
  | UpdateBalance BalanceUpdate
  | SetAlertLevel AlertLevel
  | UpdateBalanceMetrics BalanceMetrics
  
  -- Session
  | SetSession SessionState
  | UpdateSession SessionUpdate
  | ClearSession
  | AddMessage Message
  | UpdateMessage String MessageUpdate
  | SetStreaming Boolean
  
  -- Proof
  | SetProofConnected Boolean
  | SetCurrentFile (Maybe String)
  | SetGoals (Array ProofGoal)
  | SetDiagnostics (Array Diagnostic)
  | SetSuggestions (Array TacticSuggestion)
  
  -- Timeline
  | SetSnapshots (Array SnapshotSummary)
  | SelectSnapshot (Maybe String)
  | AddSnapshot SnapshotSummary
  
  -- UI
  | Navigate Route
  | ToggleSidebar
  | OpenCommandPalette
  | CloseCommandPalette
  | SetTimeRange TimeRange
  | ToggleMessageExpand String
  | AddNotification Notification
  | DismissNotification String
  
  -- Settings
  | SetTheme Theme
  | SetAlertThresholds AlertThresholds
  | ToggleVimMode
  | SetFeatureFlag String Boolean
  
  -- Batch (for initial sync)
  | BatchActions (Array Action)

-- Partial update types
type BalanceUpdate =
  { diem :: Maybe Number
  , usd :: Maybe Number
  , effective :: Maybe Number
  , lastUpdated :: Maybe DateTime
  }

type SessionUpdate =
  { promptTokens :: Maybe Int
  , completionTokens :: Maybe Int
  , cost :: Maybe Number
  }

type MessageUpdate =
  { content :: Maybe String
  , isComplete :: Maybe Boolean
  }
```

---

## Reducer

### Pure State Transitions

```purescript
module Sidepanel.State.Reducer where

import Prelude
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Array as Array
import Data.Set as Set
import Sidepanel.State.AppState (AppState)
import Sidepanel.State.Actions (Action(..))

-- Pure reducer function
reduce :: AppState -> Action -> AppState
reduce state action = case action of
  -- Connection
  SetConnected connected ->
    state { connected = connected }
  
  SetLastSyncTime time ->
    state { lastSyncTime = Just time }
  
  -- Balance
  UpdateBalance update ->
    state { balance = mergeBalance state.balance update }
  
  SetAlertLevel level ->
    state { balance = state.balance { alertLevel = level } }
  
  UpdateBalanceMetrics metrics ->
    state { balance = state.balance { metrics = metrics } }
  
  -- Session
  SetSession session ->
    state { session = Just session }
  
  UpdateSession update ->
    state { session = map (mergeSession update) state.session }
  
  ClearSession ->
    state { session = Nothing }
  
  AddMessage message ->
    state { session = map addMessageToSession state.session }
    where
      addMessageToSession s = s { messages = Array.snoc s.messages message }
  
  UpdateMessage id update ->
    state { session = map (updateMessageInSession id update) state.session }
  
  SetStreaming streaming ->
    state { session = map (_ { isStreaming = streaming }) state.session }
  
  -- Proof
  SetProofConnected connected ->
    state { proof = state.proof { connected = connected } }
  
  SetCurrentFile file ->
    state { proof = state.proof { currentFile = file } }
  
  SetGoals goals ->
    state { proof = state.proof { goals = goals } }
  
  SetDiagnostics diagnostics ->
    state { proof = state.proof { diagnostics = diagnostics } }
  
  SetSuggestions suggestions ->
    state { proof = state.proof { suggestions = suggestions } }
  
  -- Timeline
  SetSnapshots snapshots ->
    state { snapshots = snapshots }
  
  SelectSnapshot id ->
    state { selectedSnapshotId = id }
  
  AddSnapshot snapshot ->
    state { snapshots = Array.cons snapshot state.snapshots }
  
  -- UI
  Navigate route ->
    state { ui = state.ui { currentRoute = route } }
  
  ToggleSidebar ->
    state { ui = state.ui { sidebarCollapsed = not state.ui.sidebarCollapsed } }
  
  OpenCommandPalette ->
    state { ui = state.ui { commandPaletteOpen = true } }
  
  CloseCommandPalette ->
    state { ui = state.ui { commandPaletteOpen = false } }
  
  SetTimeRange range ->
    state { ui = state.ui { selectedTimeRange = range } }
  
  ToggleMessageExpand id ->
    state { ui = state.ui { expandedMessages = toggleSet id state.ui.expandedMessages } }
  
  AddNotification notification ->
    state { ui = state.ui { notifications = Array.cons notification state.ui.notifications } }
  
  DismissNotification id ->
    state { ui = state.ui { notifications = Array.filter (\n -> n.id /= id) state.ui.notifications } }
  
  -- Settings
  SetTheme theme ->
    state { settings = state.settings { theme = theme } }
  
  SetAlertThresholds thresholds ->
    state { settings = state.settings { alertThresholds = thresholds } }
  
  ToggleVimMode ->
    state { settings = state.settings { vimMode = not state.settings.vimMode } }
  
  SetFeatureFlag flag enabled ->
    state { settings = state.settings { features = setFlag flag enabled state.settings.features } }
  
  -- Batch
  BatchActions actions ->
    foldl reduce state actions

-- Helper functions
mergeBalance :: BalanceState -> BalanceUpdate -> BalanceState
mergeBalance current update =
  { diem: fromMaybe current.diem update.diem
  , usd: fromMaybe current.usd update.usd
  , effective: fromMaybe current.effective update.effective
  , lastUpdated: update.lastUpdated <|> current.lastUpdated
  , alertLevel: current.alertLevel  -- Updated separately
  , metrics: current.metrics
  }

mergeSession :: SessionUpdate -> SessionState -> SessionState
mergeSession update session =
  session
    { promptTokens = fromMaybe session.promptTokens update.promptTokens
    , completionTokens = fromMaybe session.completionTokens update.completionTokens
    , cost = fromMaybe session.cost update.cost
    }

toggleSet :: forall a. Ord a => a -> Set a -> Set a
toggleSet x set =
  if Set.member x set
  then Set.delete x set
  else Set.insert x set
```

---

## Store Implementation

### Store Class

```purescript
module Sidepanel.State.Store where

import Prelude
import Effect (Effect)
import Effect.Ref (Ref, new, read, write)
import Data.Array ((:))

-- Store type
newtype Store = Store
  { stateRef :: Ref AppState
  , listenersRef :: Ref (Array (AppState -> Effect Unit))
  , middlewareRef :: Ref (Array Middleware)
  }

type Middleware = Store -> Action -> Effect Action

-- Create store with initial state
createStore :: AppState -> Effect Store
createStore initialState = do
  stateRef <- new initialState
  listenersRef <- new []
  middlewareRef <- new []
  pure $ Store { stateRef, listenersRef, middlewareRef }

-- Get current state
getState :: Store -> Effect AppState
getState (Store { stateRef }) = read stateRef

-- Dispatch action
dispatch :: Store -> Action -> Effect Unit
dispatch store@(Store { stateRef, listenersRef, middlewareRef }) action = do
  -- Run through middleware
  middlewares <- read middlewareRef
  finalAction <- applyMiddleware store middlewares action
  
  -- Update state
  currentState <- read stateRef
  let newState = reduce currentState finalAction
  write newState stateRef
  
  -- Notify listeners
  listeners <- read listenersRef
  for_ listeners \listener -> listener newState

-- Subscribe to state changes
subscribe :: Store -> (AppState -> Effect Unit) -> Effect (Effect Unit)
subscribe (Store { listenersRef }) listener = do
  listeners <- read listenersRef
  write (listener : listeners) listenersRef
  
  -- Return unsubscribe function
  pure do
    currentListeners <- read listenersRef
    write (filter (\l -> l /= listener) currentListeners) listenersRef

-- Add middleware
addMiddleware :: Store -> Middleware -> Effect Unit
addMiddleware (Store { middlewareRef }) middleware = do
  middlewares <- read middlewareRef
  write (middleware : middlewares) middlewareRef

-- Apply middleware chain
applyMiddleware :: Store -> Array Middleware -> Action -> Effect Action
applyMiddleware store middlewares action =
  foldr (\mw acc -> mw store =<< acc) (pure action) middlewares
```

---

## Selectors

### Derived State

```purescript
module Sidepanel.State.Selectors where

import Prelude
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Array as Array
import Sidepanel.State.AppState

-- Balance selectors
selectBalance :: AppState -> BalanceState
selectBalance = _.balance

selectEffectiveBalance :: AppState -> Number
selectEffectiveBalance state = state.balance.effective

selectAlertLevel :: AppState -> AlertLevel
selectAlertLevel state = state.balance.alertLevel

selectTimeToDepletion :: AppState -> Maybe Number
selectTimeToDepletion state = state.balance.metrics.timeToDepletion

-- Session selectors
selectSession :: AppState -> Maybe SessionState
selectSession = _.session

selectSessionCost :: AppState -> Number
selectSessionCost state = fromMaybe 0.0 (map _.cost state.session)

selectTotalTokens :: AppState -> Int
selectTotalTokens state = case state.session of
  Nothing -> 0
  Just s -> s.promptTokens + s.completionTokens

selectMessageCount :: AppState -> Int
selectMessageCount state = fromMaybe 0 (map (Array.length <<< _.messages) state.session)

-- Proof selectors
selectProof :: AppState -> ProofState
selectProof = _.proof

selectGoalCount :: AppState -> Int
selectGoalCount state = Array.length state.proof.goals

selectHasProofErrors :: AppState -> Boolean
selectHasProofErrors state =
  Array.any (\d -> d.severity == Error) state.proof.diagnostics

-- UI selectors
selectCurrentRoute :: AppState -> Route
selectCurrentRoute state = state.ui.currentRoute

selectIsSidebarCollapsed :: AppState -> Boolean
selectIsSidebarCollapsed state = state.ui.sidebarCollapsed

selectNotifications :: AppState -> Array Notification
selectNotifications state = state.ui.notifications

-- Computed selectors (combine multiple)
selectDashboardData :: AppState -> DashboardData
selectDashboardData state =
  { balance: selectBalance state
  , sessionCost: selectSessionCost state
  , tokenCount: selectTotalTokens state
  , alertLevel: selectAlertLevel state
  , isConnected: state.connected
  }
```

---

## Middleware

### Logging Middleware

```purescript
-- Log all actions in development
loggingMiddleware :: Middleware
loggingMiddleware store action = do
  state <- getState store
  log $ "Action: " <> show action
  log $ "Prev state: " <> show state
  pure action
```

### Persistence Middleware

```purescript
-- Persist certain state to localStorage
persistenceMiddleware :: Middleware
persistenceMiddleware store action = do
  -- After certain actions, persist state
  case action of
    SetTheme theme -> 
      saveToStorage "theme" (show theme)
    ToggleSidebar -> do
      state <- getState store
      saveToStorage "sidebarCollapsed" (show state.ui.sidebarCollapsed)
    SetAlertThresholds thresholds ->
      saveToStorage "alertThresholds" (encodeJson thresholds)
    _ -> pure unit
  
  pure action
```

### WebSocket Middleware

```purescript
-- Send certain actions to bridge
websocketMiddleware :: WebSocket -> Middleware
websocketMiddleware ws store action = do
  case action of
    -- Forward to bridge
    SetAlertThresholds thresholds ->
      sendMessage ws { method: "alerts.configure", params: thresholds }
    _ -> pure unit
  
  pure action
```

---

## Component Integration

### Using Store in Components

```purescript
module Sidepanel.Components.Example where

import Sidepanel.State.Store (Store, getState, dispatch, subscribe)
import Sidepanel.State.Selectors (selectBalance)

component :: forall q i o m. MonadAff m => Store -> H.Component q i o m
component store = H.mkComponent
  { initialState: const { balance: initialBalance }
  , render
  , eval: H.mkEval $ H.defaultEval
      { initialize = Just Initialize
      , handleAction = handleAction store
      }
  }

handleAction :: forall o m. MonadAff m 
             => Store -> Action -> H.HalogenM State Action () o m Unit
handleAction store = case _ of
  Initialize -> do
    -- Subscribe to store
    unsubscribe <- H.liftEffect $ subscribe store \appState -> do
      -- Update local state when store changes
      H.modify_ _ { balance = selectBalance appState }
    
    -- Store unsubscribe for cleanup
    H.modify_ _ { unsubscribe = Just unsubscribe }
    
    -- Get initial state
    appState <- H.liftEffect $ getState store
    H.modify_ _ { balance = selectBalance appState }
  
  UpdateThreshold threshold -> do
    -- Dispatch to store
    H.liftEffect $ dispatch store (SetAlertThresholds threshold)
```

---

## Testing

```purescript
module Test.State.ReducerSpec where

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: Spec Unit
spec = describe "Reducer" do
  describe "UpdateBalance" do
    it "merges partial balance updates" do
      let 
        initial = initialState
        action = UpdateBalance { diem: Just 42.5, usd: Nothing, effective: Nothing, lastUpdated: Nothing }
        result = reduce initial action
      
      result.balance.diem `shouldEqual` 42.5
      result.balance.usd `shouldEqual` initial.balance.usd  -- Unchanged
  
  describe "BatchActions" do
    it "applies multiple actions in order" do
      let
        initial = initialState
        actions = BatchActions 
          [ SetConnected true
          , UpdateBalance { diem: Just 50.0, usd: Nothing, effective: Nothing, lastUpdated: Nothing }
          ]
        result = reduce initial actions
      
      result.connected `shouldEqual` true
      result.balance.diem `shouldEqual` 50.0
```

---

## Related Specifications

- `40-PURESCRIPT-ARCHITECTURE.md` - AppM monad
- `32-STATE-SYNCHRONIZATION.md` - Bridge sync
- `42-CUSTOM-HOOKS.md` - React-style hooks

---

*"Predictable state makes predictable applications."*
