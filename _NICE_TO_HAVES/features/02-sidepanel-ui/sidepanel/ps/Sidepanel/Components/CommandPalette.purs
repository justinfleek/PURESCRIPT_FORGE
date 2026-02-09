-- | Command Palette Component - Universal Command Interface
-- |
-- | **What:** Provides a command palette interface (similar to VS Code's command palette)
-- |         for executing commands via keyboard shortcuts or search. Supports filtering,
-- |         keyboard navigation, and command execution.
-- | **Why:** Enables quick access to all application commands without memorizing keyboard
-- |         shortcuts. Improves discoverability and efficiency.
-- | **How:** Renders a modal overlay with search input and filtered command list. Supports
-- |         keyboard navigation (arrow keys), Enter to execute, Escape to close. Filters
-- |         commands by name, description, or category based on query string.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Utils.Keyboard`: Keyboard shortcut types
-- | - `Sidepanel.WebSocket.Client`: WebSocket communication
-- | - `Sidepanel.Api.Bridge`: Bridge API methods for command execution
-- |
-- | **Mathematical Foundation:**
-- | - **Command Filtering:** Commands are filtered by checking if query string (lowercase)
-- |   is contained in command name, description, or category (all lowercase).
-- | - **Selection Index:** Selected command index wraps around (0 to maxIndex) when
-- |   navigating with arrow keys.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.CommandPalette as CommandPalette
-- |
-- | -- In parent component:
-- | HH.slot _palette unit CommandPalette.component
-- |   { wsClient: wsClient }
-- |   (case _ of
-- |     CommandPalette.CommandExecuted id -> HandleCommand id
-- |     CommandPalette.NavigateToRoute route -> NavigateTo route
-- |     CommandPalette.PaletteClosed -> HandlePaletteClosed)
-- |
-- | -- Open palette:
-- | H.query _palette unit $ H.tell CommandPalette.Open
-- | ```
-- |
-- | Spec 46: Universal command interface
module Sidepanel.Components.CommandPalette where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Data.Array (filter, take, length, mapWithIndex)
import Data.Maybe (Maybe(..))
import Data.String (toLower, contains, Pattern(..))
import Data.Either (Either(..))
import Sidepanel.Utils.Keyboard (KeyboardShortcut)
import Sidepanel.WebSocket.Client as WS
import Sidepanel.Api.Bridge as Bridge

-- | Command definition
type Command =
  { id :: String
  , name :: String
  , description :: String
  , category :: String
  , shortcut :: Maybe KeyboardShortcut
  , handler :: Aff Unit
  }

-- | Component input
type Input = { wsClient :: Maybe WS.WSClient }

-- | Component state
type State =
  { open :: Boolean
  , query :: String
  , commands :: Array Command
  , selectedIndex :: Int
  , filteredCommands :: Array Command
  , wsClient :: Maybe WS.WSClient
  }

-- | Component query
data Query a
  = Open a
  | Close a

-- | Component actions
data Action
  = Initialize
  | UpdateQuery String
  | SelectNext
  | SelectPrevious
  | ExecuteSelected
  | KeyPressed String

-- | Component output
data Output
  = CommandExecuted String
  | NavigateToRoute String -- Route name for navigation
  | PaletteClosed

-- | Command Palette component
component :: forall q m. MonadAff m => H.Component q Input Output m
component =
  H.mkComponent
    { initialState: \input -> initialState { wsClient = input.wsClient }
    , render
    , eval: H.mkEval $ H.defaultEval
        { handleAction = handleAction
        , handleQuery = handleQuery
        , initialize = Just Initialize
        }
    }

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  Open a -> do
    H.modify_ \s -> s { open = true, query = "", selectedIndex = 0 }
    pure (Just a)
  Close a -> do
    H.modify_ \s -> s { open = false, query = "", selectedIndex = 0 }
    pure (Just a)

initialState :: State
initialState =
  { open: false
  , query: ""
  , commands: []
  , selectedIndex: 0
  , filteredCommands: []
  , wsClient: Nothing
  }

-- | Create default commands with client access
defaultCommands :: Maybe WS.WSClient -> Array Command
defaultCommands wsClient =
  [ -- Session Commands
    { id: "new-session"
    , name: "New Session"
    , description: "Create a new session"
    , category: "Session"
    , shortcut: Just { key: "n", ctrl: true, shift: false, alt: false }
    , handler: case wsClient of
        Just client -> Bridge.createNewSession client { name: Nothing, parentId: Nothing, model: Nothing, provider: Nothing } *> pure unit
        Nothing -> pure unit
    }
  , -- Navigation Commands
    { id: "open-settings"
    , name: "Open Settings"
    , description: "Open settings panel"
    , category: "Navigation"
    , shortcut: Just { key: ",", ctrl: true, shift: false, alt: false }
    , handler: pure unit -- Settings panel opening handled by router
    }
  , { id: "toggle-sidebar"
    , name: "Toggle Sidebar"
    , description: "Show/hide sidebar"
    , category: "Navigation"
    , shortcut: Just { key: "b", ctrl: true, shift: false, alt: false }
    , handler: pure unit -- Sidebar toggle handled by App component
    }
  , { id: "open-dashboard"
    , name: "Open Dashboard"
    , description: "Navigate to dashboard"
    , category: "Navigation"
    , shortcut: Just { key: "d", ctrl: true, shift: false, alt: false }
    , handler: pure unit -- Navigation handled by App component via output
    }
  , { id: "open-timeline"
    , name: "Open Timeline"
    , description: "Navigate to timeline view"
    , category: "Navigation"
    , shortcut: Just { key: "t", ctrl: true, shift: false, alt: false }
    , handler: pure unit -- Navigation handled by App component via output
    }
  , { id: "open-file-context"
    , name: "Open File Context"
    , description: "Navigate to file context view"
    , category: "Navigation"
    , shortcut: Just { key: "f", ctrl: true, shift: false, alt: false }
    , handler: pure unit -- Navigation handled by App component via output
    }
  , { id: "open-terminal"
    , name: "Open Terminal"
    , description: "Navigate to terminal embed"
    , category: "Navigation"
    , shortcut: Just { key: "`", ctrl: false, shift: false, alt: false }
    , handler: pure unit -- Navigation handled by App component via output
    }
  , -- Snapshot Commands
    { id: "save-snapshot"
    , name: "Save Snapshot"
    , description: "Save current state as snapshot"
    , category: "Snapshot"
    , shortcut: Just { key: "s", ctrl: true, shift: true, alt: false }
    , handler: case wsClient of
        Just client -> Bridge.saveSnapshot client { trigger: "manual", description: Nothing } *> pure unit
        Nothing -> pure unit
    }
  , { id: "list-snapshots"
    , name: "List Snapshots"
    , description: "View all saved snapshots"
    , category: "Snapshot"
    , shortcut: Nothing
    , handler: pure unit -- Opens timeline view which shows snapshots
    }
  , -- File Context Commands
    { id: "refresh-file-context"
    , name: "Refresh File Context"
    , description: "Reload files in context"
    , category: "File Context"
    , shortcut: Just { key: "r", ctrl: true, shift: false, alt: false }
    , handler: pure unit -- File context refresh handled by FileContextView component
    }
  , -- Lean Commands
    { id: "lean-check-file"
    , name: "Lean: Check File"
    , description: "Run Lean check on current file"
    , category: "Lean"
    , shortcut: Just { key: "l", ctrl: true, shift: true, alt: false }
    , handler: pure unit -- Lean check handled by ProofPanel
    }
  , { id: "lean-goals"
    , name: "Lean: Show Goals"
    , description: "Show Lean goals at cursor"
    , category: "Lean"
    , shortcut: Just { key: "g", ctrl: true, shift: false, alt: false }
    , handler: pure unit -- Lean goals handled by ProofPanel
    }
  , -- Utility Commands
    { id: "open-command-palette"
    , name: "Open Command Palette"
    , description: "Open command palette (this menu)"
    , category: "Utility"
    , shortcut: Just { key: "p", ctrl: true, shift: false, alt: false }
    , handler: pure unit -- Command palette opening handled by App component
    }
  , { id: "show-keyboard-shortcuts"
    , name: "Show Keyboard Shortcuts"
    , description: "Display all keyboard shortcuts"
    , category: "Utility"
    , shortcut: Just { key: "?", ctrl: false, shift: false, alt: false }
    , handler: pure unit -- Shortcuts help handled by KeyboardNavigation
    }
  ]

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  if state.open then
    HH.div
      [ HP.class_ (H.ClassName "command-palette-overlay")
      , HE.onClick \_ -> H.raise PaletteClosed
      ]
      [ HH.div
          [ HP.class_ (H.ClassName "command-palette")
          , HE.onClick \e -> H.stopPropagation e
          ]
          [ HH.input
              [ HP.class_ (H.ClassName "command-palette-input")
              , HP.type_ HP.InputText
              , HP.placeholder "Type a command..."
              , HP.value state.query
              , HE.onValueInput UpdateQuery
              , HE.onKeyDown \e -> KeyPressed e.key
              ]
          , HH.div
              [ HP.class_ (H.ClassName "command-palette-results") ]
              (mapWithIndex (renderCommand state.selectedIndex) state.filteredCommands)
          ]
      ]
  else
    HH.text ""

renderCommand :: forall m. Int -> Int -> Command -> H.ComponentHTML Action () m
renderCommand selectedIndex index command =
  HH.div
    [ HP.class_ (H.ClassName $ "command-item" <> if index == selectedIndex then " selected" else "")
    , HE.onClick \_ -> ExecuteSelected
    ]
    [ HH.div
        [ HP.class_ (H.ClassName "command-name") ]
        [ HH.text command.name ]
    , HH.div
        [ HP.class_ (H.ClassName "command-description") ]
        [ HH.text command.description ]
    , case command.shortcut of
        Just shortcut ->
          HH.div
            [ HP.class_ (H.ClassName "command-shortcut") ]
            [ HH.text (formatShortcut shortcut) ]
        Nothing ->
          HH.text ""
    ]

formatShortcut :: KeyboardShortcut -> String
formatShortcut s =
  (if s.ctrl then "Ctrl+" else "")
    <> (if s.shift then "Shift+" else "")
    <> (if s.alt then "Alt+" else "")
    <> s.key

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    state <- H.get
    -- Update commands with client access
    let updatedCommands = defaultCommands state.wsClient
    H.modify_ \s ->
      { s
      | commands = updatedCommands
      , filteredCommands = updatedCommands
      }
  
  UpdateQuery query -> do
    H.modify_ \s ->
      { s
      | query = query
      , selectedIndex = 0
      , filteredCommands = filterCommands query s.commands
      , open = true
      }
  
  SelectNext -> do
    state <- H.get
    let maxIndex = length state.filteredCommands - 1
    H.modify_ \s ->
      { s
      | selectedIndex = min (s.selectedIndex + 1) maxIndex
      }
  
  SelectPrevious -> do
    H.modify_ \s ->
      { s
      | selectedIndex = max 0 (s.selectedIndex - 1)
      }
  
  ExecuteSelected -> do
    state <- H.get
    case state.filteredCommands !! state.selectedIndex of
      Just command -> do
        H.liftAff command.handler
        H.raise (CommandExecuted command.id)
        -- Emit navigation output for navigation commands
        case command.id of
          "open-dashboard" -> H.raise (NavigateToRoute "dashboard")
          "open-timeline" -> H.raise (NavigateToRoute "timeline")
          "open-file-context" -> H.raise (NavigateToRoute "file-context")
          "open-terminal" -> H.raise (NavigateToRoute "terminal")
          "open-settings" -> H.raise (NavigateToRoute "settings")
          "list-snapshots" -> H.raise (NavigateToRoute "timeline")
          _ -> pure unit
        H.modify_ \s -> s { open = false }
        H.raise PaletteClosed
      Nothing ->
        pure unit
  
  KeyPressed key -> do
    case key of
      "Escape" -> do
        H.modify_ \s -> s { open = false }
        H.raise PaletteClosed
      "Enter" -> handleAction ExecuteSelected
      "ArrowDown" -> handleAction SelectNext
      "ArrowUp" -> handleAction SelectPrevious
      _ -> pure unit

filterCommands :: String -> Array Command -> Array Command
filterCommands query commands =
  if query == "" then
    take 10 commands
  else
    take 10 $ filter (matchesQuery query) commands

matchesQuery :: String -> Command -> Boolean
matchesQuery query command =
  contains (Pattern $ toLower query) (toLower command.name)
    || contains (Pattern $ toLower query) (toLower command.description)
    || contains (Pattern $ toLower query) (toLower command.category)
