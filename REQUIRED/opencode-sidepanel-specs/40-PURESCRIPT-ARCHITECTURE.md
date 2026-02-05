# 40-PURESCRIPT-ARCHITECTURE: Halogen Component Architecture

## Overview

The sidepanel frontend is built with PureScript and Halogen, providing compile-time guarantees that TypeScript cannot match. This document covers the architectural patterns, component structure, and state management approach.

**Why PureScript?**
- No runtime type errors (ever)
- Row polymorphism catches API contract violations at compile time
- Algebraic data types ensure exhaustive pattern matching
- Effect tracking prevents accidental side effects
- Target audience (senior engineers) respects the choice

---

## Project Structure

```
frontend/
├── spago.yaml                    # Package manager config
├── packages.dhall                # Package set
├── src/
│   ├── Main.purs                 # Entry point
│   ├── AppM.purs                 # Application monad
│   ├── Router.purs               # SPA routing
│   ├── Config.purs               # Runtime configuration
│   │
│   ├── Api/
│   │   ├── WebSocket.purs        # WebSocket client
│   │   ├── Types.purs            # Shared API types
│   │   └── Codec.purs            # JSON encoding/decoding
│   │
│   ├── State/
│   │   ├── AppState.purs         # Global application state
│   │   ├── Balance.purs          # Diem balance state
│   │   ├── Session.purs          # Session state
│   │   ├── Proof.purs            # Lean4 proof state
│   │   └── Reducer.purs          # State update functions
│   │
│   ├── Components/
│   │   ├── App.purs              # Root component
│   │   ├── Dashboard.purs        # Main dashboard layout
│   │   ├── Sidebar.purs          # Navigation sidebar
│   │   │
│   │   ├── Balance/
│   │   │   ├── DiemTracker.purs  # Balance display
│   │   │   ├── Countdown.purs    # Reset countdown
│   │   │   └── UsageChart.purs   # Usage visualization
│   │   │
│   │   ├── Session/
│   │   │   ├── SessionPanel.purs # Current session info
│   │   │   ├── TokenCounter.purs # Token usage display
│   │   │   └── CostDisplay.purs  # Cost breakdown
│   │   │
│   │   ├── Proof/
│   │   │   ├── ProofPanel.purs   # Lean4 proof status
│   │   │   ├── GoalDisplay.purs  # Current goals
│   │   │   └── TacticList.purs   # Tactic suggestions
│   │   │
│   │   ├── Timeline/
│   │   │   ├── TimeTravel.purs   # Time-travel UI
│   │   │   ├── Snapshot.purs     # Snapshot cards
│   │   │   └── Scrubber.purs     # Timeline scrubber
│   │   │
│   │   ├── Performance/
│   │   │   ├── FlameGraph.purs   # Flame graph viz
│   │   │   └── Metrics.purs      # Performance metrics
│   │   │
│   │   └── Common/
│   │       ├── Button.purs       # Button component
│   │       ├── Card.purs         # Card container
│   │       ├── Modal.purs        # Modal dialog
│   │       ├── Tooltip.purs      # Tooltips
│   │       └── Loading.purs      # Loading states
│   │
│   ├── Hooks/
│   │   ├── UseWebSocket.purs     # WebSocket hook
│   │   ├── UseCountdown.purs     # Countdown timer hook
│   │   └── UseKeyboard.purs      # Keyboard shortcuts
│   │
│   └── Utils/
│       ├── Time.purs             # Time formatting
│       ├── Currency.purs         # Currency formatting
│       ├── Dom.purs              # DOM utilities
│       └── Keyboard.purs         # Keybinding utilities
│
├── test/
│   ├── Test/Main.purs
│   ├── Test/State/
│   └── Test/Components/
│
└── assets/
    ├── index.html
    └── styles/
        ├── main.css
        └── components/
```

---

## Application Monad

### AppM Definition

```purescript
module Sidepanel.AppM where

import Prelude
import Control.Monad.Reader (class MonadAsk, ReaderT, asks, runReaderT)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Sidepanel.Api.WebSocket (WebSocketClient)
import Sidepanel.Config (Config)

-- | Application environment
type Env =
  { config :: Config
  , wsClient :: WebSocketClient
  }

-- | Application monad: ReaderT over Aff
newtype AppM a = AppM (ReaderT Env Aff a)

derive newtype instance functorAppM :: Functor AppM
derive newtype instance applyAppM :: Apply AppM
derive newtype instance applicativeAppM :: Applicative AppM
derive newtype instance bindAppM :: Bind AppM
derive newtype instance monadAppM :: Monad AppM
derive newtype instance monadEffectAppM :: MonadEffect AppM
derive newtype instance monadAffAppM :: MonadAff AppM
derive newtype instance monadAskAppM :: MonadAsk Env AppM

-- | Run AppM with environment
runAppM :: forall a. Env -> AppM a -> Aff a
runAppM env (AppM m) = runReaderT m env

-- | Capability: access WebSocket client
class Monad m <= MonadWebSocket m where
  getWsClient :: m WebSocketClient

instance monadWebSocketAppM :: MonadWebSocket AppM where
  getWsClient = AppM $ asks _.wsClient

-- | Capability: access config
class Monad m <= MonadConfig m where
  getConfig :: m Config

instance monadConfigAppM :: MonadConfig AppM where
  getConfig = AppM $ asks _.config
```

### Lifting to Halogen

```purescript
module Sidepanel.AppM.Halogen where

import Halogen as H
import Sidepanel.AppM (AppM)

-- | Type alias for Halogen components using AppM
type Component q i o = H.Component q i o AppM

-- | Type alias for HalogenM using AppM
type HalogenM s a cs o = H.HalogenM s a cs o AppM
```

---

## State Management

### Global State Structure

```purescript
module Sidepanel.State.AppState where

import Data.Maybe (Maybe)
import Data.DateTime (DateTime)

-- | Complete application state
type AppState =
  { -- Connection status
    connected :: Boolean
    lastPing :: Maybe DateTime
    
    -- Balance state
  , balance :: BalanceState
  
    -- Session state
  , session :: Maybe SessionState
  
    -- Proof state (Lean4)
  , proof :: ProofState
  
    -- Timeline/snapshots
  , snapshots :: Array Snapshot
  , selectedSnapshot :: Maybe SnapshotId
  
    -- UI state
  , sidebarCollapsed :: Boolean
  , activePanel :: Panel
  , theme :: Theme
  
    -- Alerts
  , alerts :: Array Alert
  }

type BalanceState =
  { diem :: Number
  , usd :: Number
  , effective :: Number
  , metrics :: BalanceMetrics
  , countdown :: Countdown
  }

type SessionState =
  { id :: SessionId
  , promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cost :: Number
  , model :: String
  , messageCount :: Int
  , startedAt :: DateTime
  }

type ProofState =
  { connected :: Boolean
  , currentFile :: Maybe FilePath
  , goals :: Array Goal
  , diagnostics :: Array Diagnostic
  , suggestedTactics :: Array Tactic
  }

data Panel
  = DashboardPanel
  | SessionPanel
  | ProofPanel
  | TimelinePanel
  | SettingsPanel

derive instance eqPanel :: Eq Panel
```

### State Actions

```purescript
module Sidepanel.State.Actions where

import Sidepanel.State.AppState

-- | All possible state actions
data Action
  -- Connection
  = Connected
  | Disconnected
  | PingReceived DateTime
  
  -- Balance
  | BalanceUpdated BalanceState
  | CountdownTick
  
  -- Session
  | SessionUpdated SessionState
  | SessionCleared
  | UsageRecorded UsageRecord
  
  -- Proof
  | ProofConnected
  | ProofDisconnected
  | GoalsUpdated (Array Goal)
  | DiagnosticsUpdated (Array Diagnostic)
  | TacticsUpdated (Array Tactic)
  
  -- Timeline
  | SnapshotCreated Snapshot
  | SnapshotSelected SnapshotId
  | SnapshotRestored SnapshotId
  
  -- UI
  | ToggleSidebar
  | SetActivePanel Panel
  | SetTheme Theme
  | DismissAlert AlertId
  
  -- Alerts
  | AlertTriggered Alert
```

### Reducer

```purescript
module Sidepanel.State.Reducer where

import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Sidepanel.State.AppState
import Sidepanel.State.Actions

-- | Pure state reducer
reduce :: AppState -> Action -> AppState
reduce state = case _ of
  Connected ->
    state { connected = true }
  
  Disconnected ->
    state { connected = false }
  
  PingReceived timestamp ->
    state { lastPing = Just timestamp }
  
  BalanceUpdated balance ->
    state { balance = balance }
  
  CountdownTick ->
    state { balance = updateCountdown state.balance }
  
  SessionUpdated session ->
    state { session = Just session }
  
  SessionCleared ->
    state { session = Nothing }
  
  UsageRecorded usage ->
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
  
  SnapshotCreated snapshot ->
    state { snapshots = Array.snoc state.snapshots snapshot }
  
  SnapshotSelected id ->
    state { selectedSnapshot = Just id }
  
  ToggleSidebar ->
    state { sidebarCollapsed = not state.sidebarCollapsed }
  
  SetActivePanel panel ->
    state { activePanel = panel }
  
  SetTheme theme ->
    state { theme = theme }
  
  AlertTriggered alert ->
    state { alerts = Array.snoc state.alerts alert }
  
  DismissAlert id ->
    state { alerts = Array.filter (\a -> a.id /= id) state.alerts }

  _ -> state

-- | Helper to update countdown
updateCountdown :: BalanceState -> BalanceState
updateCountdown balance =
  balance { countdown = tickCountdown balance.countdown }
```

---

## Component Patterns

### Basic Component Template

```purescript
module Sidepanel.Components.Example where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)

-- | Component input
type Input = { initialValue :: Int }

-- | Component output (events emitted to parent)
data Output = ValueChanged Int

-- | Internal state
type State = 
  { value :: Int 
  , loading :: Boolean
  }

-- | Internal actions
data Action
  = Initialize
  | Increment
  | Decrement
  | SetValue Int

-- | Component definition
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

initialState :: Input -> State
initialState { initialValue } =
  { value: initialValue
  , loading: false
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.classes [ H.ClassName "example-component" ] ]
    [ HH.button
        [ HE.onClick \_ -> Decrement ]
        [ HH.text "-" ]
    , HH.span_
        [ HH.text $ show state.value ]
    , HH.button
        [ HE.onClick \_ -> Increment ]
        [ HH.text "+" ]
    ]

handleAction :: forall m. MonadAff m 
             => Action 
             -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize ->
    pure unit
  
  Increment -> do
    H.modify_ \s -> s { value = s.value + 1 }
    { value } <- H.get
    H.raise $ ValueChanged value
  
  Decrement -> do
    H.modify_ \s -> s { value = s.value - 1 }
    { value } <- H.get
    H.raise $ ValueChanged value
  
  SetValue v -> do
    H.modify_ _ { value = v }
    H.raise $ ValueChanged v
```

### Component with Subscriptions

```purescript
module Sidepanel.Components.WithSubscription where

import Prelude
import Halogen as H
import Halogen.Subscription as HS
import Effect.Aff (Milliseconds(..), delay)
import Effect.Aff.Class (class MonadAff, liftAff)

data Action
  = Initialize
  | Tick

component :: forall q i o m. MonadAff m => H.Component q i o m
component = H.mkComponent
  { initialState: \_ -> { count: 0 }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

handleAction :: forall o m. MonadAff m 
             => Action 
             -> H.HalogenM { count :: Int } Action () o m Unit
handleAction = case _ of
  Initialize -> do
    -- Subscribe to timer
    _ <- H.subscribe $ timer Tick
    pure unit
  
  Tick ->
    H.modify_ \s -> s { count = s.count + 1 }

-- | Timer emitter that fires every second
timer :: forall m. MonadAff m => Action -> HS.Emitter m Action
timer action = HS.makeEmitter \push -> do
  -- Fork a fiber that pushes action every second
  fiber <- liftAff $ forkAff $ forever do
    delay (Milliseconds 1000.0)
    liftEffect $ push action
  -- Return canceller
  pure $ liftAff $ killFiber (error "unsubscribed") fiber
```

### Component with Child Slots

```purescript
module Sidepanel.Components.Parent where

import Prelude
import Type.Proxy (Proxy(..))
import Halogen as H
import Halogen.HTML as HH
import Sidepanel.Components.DiemTracker as DiemTracker
import Sidepanel.Components.Countdown as Countdown

-- | Slot types for children
type Slots =
  ( diemTracker :: H.Slot DiemTracker.Query DiemTracker.Output Unit
  , countdown :: H.Slot Countdown.Query Countdown.Output Unit
  )

_diemTracker = Proxy :: Proxy "diemTracker"
_countdown = Proxy :: Proxy "countdown"

render :: forall m. State -> H.ComponentHTML Action Slots m
render state =
  HH.div_
    [ -- Child component with slot
      HH.slot _diemTracker unit DiemTracker.component 
        { balance: state.balance } 
        HandleDiemOutput
    
    , HH.slot _countdown unit Countdown.component
        { targetTime: state.resetTime }
        HandleCountdownOutput
    ]

data Action
  = HandleDiemOutput DiemTracker.Output
  | HandleCountdownOutput Countdown.Output

handleAction = case _ of
  HandleDiemOutput (DiemTracker.AlertTriggered alert) ->
    -- Handle child output
    H.modify_ \s -> s { alerts = Array.snoc s.alerts alert }
  
  HandleCountdownOutput Countdown.ResetOccurred ->
    -- Handle countdown reaching zero
    refreshBalance
```

---

## Hooks Pattern

### Custom Hook: useWebSocket

```purescript
module Sidepanel.Hooks.UseWebSocket where

import Prelude
import Halogen.Hooks as Hooks
import Halogen.Hooks (Hook, UseState, UseEffect)
import Effect.Aff.Class (class MonadAff)
import Sidepanel.Api.WebSocket (ServerMessage)

-- | Hook for WebSocket subscription
useWebSocket 
  :: forall m
   . MonadAff m
  => (ServerMessage -> Hooks.HookM m Unit)
  -> Hook m (UseEffect (UseState Boolean Unit)) Boolean
useWebSocket handler = Hooks.do
  connected /\ connectedId <- Hooks.useState false
  
  Hooks.useLifecycleEffect do
    -- Connect on mount
    ws <- Hooks.lift $ connectWebSocket
    
    -- Subscribe to messages
    unsubscribe <- Hooks.lift $ ws.subscribe \msg -> do
      handler msg
    
    Hooks.put connectedId true
    
    -- Return cleanup
    pure $ Just do
      unsubscribe
      ws.close
  
  Hooks.pure connected
```

### Custom Hook: useCountdown

```purescript
module Sidepanel.Hooks.UseCountdown where

import Prelude
import Halogen.Hooks as Hooks
import Data.DateTime (DateTime)
import Sidepanel.Utils.Time (getTimeUntilReset, TimeRemaining)

type UseCountdown = UseState TimeRemaining (UseEffect Unit)

useCountdown :: forall m. MonadAff m => Hook m UseCountdown TimeRemaining
useCountdown = Hooks.do
  time /\ timeId <- Hooks.useState initialTime
  
  Hooks.useLifecycleEffect do
    -- Start timer
    intervalId <- Hooks.lift $ setInterval 1000 do
      newTime <- getTimeUntilReset
      Hooks.put timeId newTime
    
    -- Cleanup
    pure $ Just $ clearInterval intervalId
  
  Hooks.pure time
  where
    initialTime = { hours: 0, minutes: 0, seconds: 0, totalMs: 0.0 }
```

---

## Routing

### Route Definition

```purescript
module Sidepanel.Router where

import Prelude
import Data.Generic.Rep (class Generic)
import Routing.Duplex (RouteDuplex', root, segment, param)
import Routing.Duplex.Generic (sum, noArgs)

-- | Application routes
data Route
  = Dashboard
  | Session
  | Proof
  | Timeline
  | Settings
  | NotFound

derive instance genericRoute :: Generic Route _
derive instance eqRoute :: Eq Route

-- | Route codec
routeCodec :: RouteDuplex' Route
routeCodec = root $ sum
  { "Dashboard": noArgs
  , "Session": segment "session" *> noArgs
  , "Proof": segment "proof" *> noArgs
  , "Timeline": segment "timeline" *> noArgs
  , "Settings": segment "settings" *> noArgs
  , "NotFound": noArgs
  }

-- | Parse URL to route
parseRoute :: String -> Route
parseRoute url = case parse routeCodec url of
  Right route -> route
  Left _ -> NotFound

-- | Print route to URL
printRoute :: Route -> String
printRoute = print routeCodec
```

### Router Component

```purescript
module Sidepanel.Components.Router where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Routing.Hash (matchesWith)
import Sidepanel.Router (Route(..), parseRoute)
import Sidepanel.Components.Dashboard as Dashboard
import Sidepanel.Components.Session as Session
import Sidepanel.Components.Proof as Proof
import Sidepanel.Components.Timeline as Timeline
import Sidepanel.Components.Settings as Settings

type State = { route :: Route }

data Action
  = Initialize
  | NavigateTo Route

component :: forall q i o m. MonadAff m => H.Component q i o m
component = H.mkComponent
  { initialState: \_ -> { route: Dashboard }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

render :: forall m. State -> H.ComponentHTML Action Slots m
render { route } = case route of
  Dashboard -> HH.slot_ _dashboard unit Dashboard.component {}
  Session -> HH.slot_ _session unit Session.component {}
  Proof -> HH.slot_ _proof unit Proof.component {}
  Timeline -> HH.slot_ _timeline unit Timeline.component {}
  Settings -> HH.slot_ _settings unit Settings.component {}
  NotFound -> HH.div_ [ HH.text "Page not found" ]

handleAction = case _ of
  Initialize -> do
    -- Subscribe to hash changes
    void $ H.subscribe $ hashChangeEmitter NavigateTo
  
  NavigateTo route ->
    H.modify_ _ { route = route }

-- | Emitter for hash changes
hashChangeEmitter :: forall m. MonadAff m => (Route -> Action) -> HS.Emitter m Action
hashChangeEmitter toAction = HS.makeEmitter \push -> do
  liftEffect $ matchesWith parseRoute \_ new -> push (toAction new)
```

---

## FFI Patterns

### JavaScript Interop

```purescript
-- | Foreign import for xterm.js
module Sidepanel.FFI.XTerm where

import Prelude
import Effect (Effect)
import Web.HTML.HTMLElement (HTMLElement)

-- | Terminal instance (opaque foreign type)
foreign import data Terminal :: Type

-- | Create new terminal
foreign import createTerminal :: Effect Terminal

-- | Open terminal in DOM element
foreign import openTerminal :: Terminal -> HTMLElement -> Effect Unit

-- | Write to terminal
foreign import writeTerminal :: Terminal -> String -> Effect Unit

-- | Subscribe to data events
foreign import onData :: Terminal -> (String -> Effect Unit) -> Effect (Effect Unit)

-- | Dispose terminal
foreign import disposeTerminal :: Terminal -> Effect Unit
```

```javascript
// FFI implementation: XTerm.js
import { Terminal } from 'xterm';
import { FitAddon } from 'xterm-addon-fit';

export const createTerminal = () => {
  const term = new Terminal({
    fontFamily: 'JetBrains Mono, monospace',
    fontSize: 14,
    theme: {
      background: '#1a1a1a',
      foreground: '#e4e4e7'
    }
  });
  const fitAddon = new FitAddon();
  term.loadAddon(fitAddon);
  term._fitAddon = fitAddon;
  return term;
};

export const openTerminal = term => element => () => {
  term.open(element);
  term._fitAddon.fit();
};

export const writeTerminal = term => data => () => {
  term.write(data);
};

export const onData = term => callback => () => {
  const disposable = term.onData(data => callback(data)());
  return () => disposable.dispose();
};

export const disposeTerminal = term => () => {
  term.dispose();
};
```

---

## Build Configuration

### spago.yaml

```yaml
package:
  name: sidepanel
  dependencies:
    - aff
    - affjax
    - argonaut
    - arrays
    - console
    - datetime
    - effect
    - either
    - foldable-traversable
    - halogen
    - halogen-hooks
    - maybe
    - prelude
    - routing-duplex
    - strings
    - transformers
    - web-html
    - web-socket

workspace:
  packageSet:
    registry: 51.3.0
  extraPackages: {}
```

### Build Scripts

```bash
# Development build with watch
spago build --watch

# Production build
spago bundle-app --to dist/app.js --minify

# Run tests
spago test
```

---

## Testing

### Component Test Example

```purescript
module Test.Components.Countdown where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Halogen.Test.Driver (runUI)
import Sidepanel.Components.Countdown as Countdown

spec :: Spec Unit
spec = describe "Countdown Component" do
  it "displays formatted time" do
    let input = { targetTime: someDateTime }
    result <- runUI Countdown.component input
    
    -- Query component state
    state <- result.query Countdown.GetState
    state.formatted `shouldEqual` "4h 23m 17s"
  
  it "updates on tick" do
    let input = { targetTime: someDateTime }
    result <- runUI Countdown.component input
    
    -- Trigger tick
    result.send Countdown.Tick
    
    -- Verify update
    state <- result.query Countdown.GetState
    state.totalSeconds `shouldEqual` (originalSeconds - 1)
```

---

## Related Specifications

- `41-COMPONENT-HIERARCHY.md` - Full component tree
- `42-STATE-MANAGEMENT.md` - State patterns in depth
- `43-WEBSOCKET-CLIENT.md` - WebSocket integration
- `47-THEMING.md` - Theme system
- `48-KEYBOARD-NAVIGATION.md` - Vim bindings

---

*"Types are not constraints—they are proofs that your code is correct."*
