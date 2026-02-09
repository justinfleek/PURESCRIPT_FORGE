-- | Terminal Embed Component - Integrated Terminal Interface
-- |
-- | **What:** Provides an integrated terminal interface using xterm.js, allowing users to
-- |         execute shell commands directly from the sidepanel. Commands are executed via
-- |         Bridge Server.
-- | **Why:** Enables users to run terminal commands without leaving the editor, improving
-- |         workflow efficiency. Useful for running build commands, git operations, and
-- |         other CLI tasks.
-- | **How:** Creates xterm.js terminal instance, handles user input, sends commands to
-- |         Bridge Server via `terminal.execute` method, and displays output in the terminal.
-- |         Supports clearing terminal and toggling visibility.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.FFI.XTerm`: xterm.js FFI bindings
-- | - `Sidepanel.WebSocket.Client`: WebSocket communication
-- | - `Sidepanel.Api.Bridge`: Bridge API methods for terminal operations
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.TerminalEmbed as TerminalEmbed
-- |
-- | -- In parent component:
-- | HH.slot _terminal unit TerminalEmbed.component
-- |   { wsClient: wsClient }
-- |   (case _ of
-- |     TerminalEmbed.TerminalReady -> HandleTerminalReady
-- |     TerminalEmbed.CommandExecuted cmd -> HandleCommandExecuted cmd
-- |     TerminalEmbed.TerminalError msg -> HandleTerminalError msg)
-- | ```
-- |
-- | Spec 57: Integrated terminal view using xterm.js
module Sidepanel.Components.TerminalEmbed where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff (Aff, launchAff_)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Effect (Effect)
import Data.Maybe (Maybe(..))
import Data.Array (snoc)
import Data.Either (Either(..))
import Effect.Now (nowMillis)
import Sidepanel.FFI.XTerm as XTerm
import Sidepanel.WebSocket.Client as WS
import Sidepanel.Api.Bridge as Bridge

-- | Terminal state
type TerminalState =
  { terminal :: Maybe XTerm.Terminal
  , elementId :: String
  , connected :: Boolean
  , output :: Array String
  , inputBuffer :: String
  }

-- | Component input
type Input = { wsClient :: Maybe WS.WSClient }

-- | Component state
type State =
  { terminalState :: TerminalState
  , visible :: Boolean
  , autoScroll :: Boolean
  , wsClient :: Maybe WS.WSClient
  }

-- | Component actions
data Action
  = Initialize
  | MountTerminal
  | HandleInput String
  | ClearTerminal
  | ToggleVisibility
  | ToggleAutoScroll
  | WriteOutput String
  | Resize Int Int

-- | Component output
data Output
  = TerminalReady
  | CommandExecuted String
  | TerminalError String

-- | Terminal Embed component
component :: forall q m. MonadAff m => H.Component q Input Output m
component =
  H.mkComponent
    { initialState: \input -> initialState { wsClient = input.wsClient }
    , render
    , eval: H.mkEval $ H.defaultEval
        { handleAction = handleAction
        , initialize = Just Initialize
        }
    }

initialState :: State
initialState =
  { terminalState:
      { terminal: Nothing
      , elementId: "terminal-embed-default"
      , connected: false
      , output: []
      , inputBuffer: ""
      }
  , visible: true
  , autoScroll: true
  , wsClient: Nothing
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  if state.visible then
    HH.div
      [ HP.class_ (H.ClassName "terminal-embed") ]
      [ HH.div
          [ HP.class_ (H.ClassName "terminal-header") ]
          [ HH.h3_ [ HH.text "Terminal" ]
          , HH.div
              [ HP.class_ (H.ClassName "terminal-controls") ]
              [ HH.button
                  [ HP.class_ (H.ClassName "btn-clear")
                  , HE.onClick \_ -> ClearTerminal
                  ]
                  [ HH.text "Clear" ]
              , HH.button
                  [ HP.class_ (H.ClassName "btn-copy")
                  , HE.onClick \_ -> ToggleAutoScroll
                  ]
                  [ HH.text (if state.autoScroll then "Auto-scroll: ON" else "Auto-scroll: OFF") ]
              , HH.button
                  [ HP.class_ (H.ClassName "btn-toggle")
                  , HE.onClick \_ -> ToggleVisibility
                  ]
                  [ HH.text "Hide" ]
              ]
          ]
      , HH.div
          [ HP.id_ state.terminalState.elementId
          , HP.class_ (H.ClassName "terminal-container")
          ]
          []
      ]
  else
    HH.button
      [ HP.class_ (H.ClassName "terminal-toggle-hidden")
      , HE.onClick \_ -> ToggleVisibility
      ]
      [ HH.text "Show Terminal" ]

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Generate unique element ID using timestamp
    timestamp <- liftEffect nowMillis
    let elementId = "terminal-" <> show timestamp
    H.modify_ \s -> s { terminalState { elementId = elementId } }
    handleAction MountTerminal
  
  MountTerminal -> do
    state <- H.get
    -- Create terminal instance
    terminal <- liftEffect $ XTerm.create
      { rows: 24
      , cols: 80
      , cursorBlink: true
      , fontSize: 14
      , fontFamily: "monospace"
      , theme:
          { background: "#000000"
          , foreground: "#ffffff"
          , cursor: "#ffffff"
          , selection: "#ffffff"
          }
      }
    
    -- Open terminal in DOM element
    liftEffect $ XTerm.open terminal state.terminalState.elementId
    
    -- Set up input handler
    state <- H.get
    liftEffect $ XTerm.onData terminal \input -> do
      -- Handle user input - send to bridge server
      case state.wsClient of
        Just client -> do
          -- Execute command via bridge server (launch in background)
          void $ launchAff_ do
            result <- Bridge.executeTerminalCommand client
              { command: input
              , cwd: Nothing
              , sessionId: Nothing
              }
            case result of
              Right response -> do
                -- Write output to terminal
                case response.output of
                  Just output -> liftEffect $ XTerm.writeln terminal output
                  Nothing -> liftEffect $ XTerm.writeln terminal ("Command completed with exit code: " <> show response.exitCode)
              Left err -> do
                liftEffect $ XTerm.writeln terminal ("Error: " <> err.message)
        Nothing -> pure unit -- No client available
    
    -- Update state
    H.modify_ \s ->
      { s
      | terminalState =
          { terminal: Just terminal
          , elementId: s.terminalState.elementId
          , connected: true
          , output: []
          , inputBuffer: ""
          }
      }
    
    H.raise TerminalReady
  
  HandleInput input -> do
    state <- H.get
    case state.terminalState.terminal of
      Just terminal -> do
        liftEffect $ XTerm.write terminal input
        H.modify_ \s ->
          { s
          | terminalState { inputBuffer = s.terminalState.inputBuffer <> input }
          }
      Nothing ->
        pure unit
  
  ClearTerminal -> do
    state <- H.get
    case state.terminalState.terminal of
      Just terminal -> do
        liftEffect $ XTerm.clear terminal
        H.modify_ \s -> s { terminalState { output = [], inputBuffer = "" } }
      Nothing ->
        pure unit
  
  ToggleVisibility -> do
    H.modify_ \s -> s { visible = not s.visible }
  
  ToggleAutoScroll -> do
    H.modify_ \s -> s { autoScroll = not s.autoScroll }
  
  WriteOutput text -> do
    state <- H.get
    case state.terminalState.terminal of
      Just terminal -> do
        liftEffect $ XTerm.writeln terminal text
        H.modify_ \s ->
          { s
          | terminalState { output = snoc s.terminalState.output text }
          }
      Nothing ->
        pure unit
  
  Resize cols rows -> do
    state <- H.get
    case state.terminalState.terminal of
      Just terminal -> do
        liftEffect $ XTerm.resize terminal cols rows
      Nothing ->
        pure unit

