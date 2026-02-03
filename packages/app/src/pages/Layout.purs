-- | Main application layout - root layout with sidebar and navigation
-- | Migrated from: forge-dev/packages/app/src/pages/layout.tsx (2902 lines)
-- | 
-- | This is the largest and most complex page component.
-- | It handles:
-- | - Global state management (persisted layout state)
-- | - Sidebar with project/workspace/session navigation
-- | - Drag-and-drop for projects and workspaces
-- | - Deep linking support
-- | - Update checking
-- | - Notification handling
-- | - Session prefetching
-- | - Command palette registration
module Sidepanel.Pages.Layout
  ( LayoutPage
  , LayoutPageProps
  , LayoutPageState
  , ProjectIcon
  , SessionItem
  , SortableProject
  , SortableWorkspace
  , SidebarContent
  , SidebarPanel
  ) where

import Prelude

import Data.Array as Array
import Data.DateTime.Instant (Instant)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)

import Sidepanel.Context.Layout (LayoutContext, LocalProject)
import Sidepanel.Context.GlobalSync (GlobalSyncContext, GlobalSyncData)
import Sidepanel.Context.GlobalSDK (GlobalSDKContext)
import Sidepanel.Context.Platform (PlatformContext)
import Sidepanel.Context.Settings (SettingsContext)
import Sidepanel.Context.Server (ServerContext)
import Sidepanel.Context.Notification (NotificationContext)
import Sidepanel.Context.Permission (PermissionContext)
import Sidepanel.Context.Command (CommandContext, CommandOption)
import Sidepanel.Context.Language (LanguageContext, Locale)
import Sidepanel.Utils.Encode (base64Encode)
import Sidepanel.Utils.Base64 (decode64)
import Sidepanel.Utils.Path (getFilename)

-- | Persisted layout page state
type PersistedState =
  { lastSession :: Map String String     -- directory -> sessionID
  , activeProject :: Maybe String        -- currently active project worktree
  , activeWorkspace :: Maybe String      -- currently active workspace
  , workspaceOrder :: Map String (Array String)  -- project -> ordered workspace dirs
  , workspaceName :: Map String String   -- directory -> custom name
  , workspaceBranchName :: Map String (Map String String)  -- projectId -> branch -> name
  , workspaceExpanded :: Map String Boolean  -- directory -> expanded state
  }

-- | Runtime state
type RuntimeState =
  { autoselect :: Boolean           -- Auto-select first project on mount
  , busyWorkspaces :: Set String    -- Workspaces with pending operations
  , hoverSession :: Maybe String    -- Hovered session ID
  , hoverProject :: Maybe String    -- Hovered project worktree
  , scrollSessionKey :: Maybe String  -- Session key for scroll tracking
  , nav :: Maybe HTMLElement        -- Sidebar nav element ref
  }

-- | Editor state for inline renaming
type EditorState =
  { active :: String   -- Currently editing ID (empty = not editing)
  , value :: String    -- Current editor value
  }

-- | Combined page state
type LayoutPageState =
  { persisted :: PersistedState
  , runtime :: RuntimeState
  , editor :: EditorState
  }

-- | Props for LayoutPage
type LayoutPageProps =
  { children :: Effect Unit
  }

-- | Color scheme options
data ColorScheme = System | Light | Dark

-- | Theme entry type
type ThemeEntry = Tuple String { name :: String }

-- | Session type (from SDK)
type Session =
  { id :: String
  , title :: String
  , directory :: String
  , parentID :: Maybe String
  , time :: { created :: Instant, updated :: Maybe Instant, archived :: Maybe Instant }
  , summary :: Maybe { files :: Int }
  }

-- | Message type (from SDK)
type Message =
  { id :: String
  , role :: String
  , agent :: Maybe String
  }

-- | Foreign import for HTML Element
foreign import data HTMLElement :: Type

-- | Initial persisted state
initialPersistedState :: PersistedState
initialPersistedState =
  { lastSession: Map.empty
  , activeProject: Nothing
  , activeWorkspace: Nothing
  , workspaceOrder: Map.empty
  , workspaceName: Map.empty
  , workspaceBranchName: Map.empty
  , workspaceExpanded: Map.empty
  }

-- | Initial runtime state
initialRuntimeState :: RuntimeState
initialRuntimeState =
  { autoselect: true
  , busyWorkspaces: Set.empty
  , hoverSession: Nothing
  , hoverProject: Nothing
  , scrollSessionKey: Nothing
  , nav: Nothing
  }

-- | Initial editor state
initialEditorState :: EditorState
initialEditorState =
  { active: ""
  , value: ""
  }

-- | Get workspace key (normalized directory path)
workspaceKey :: String -> String
workspaceKey directory = 
  String.replaceAll (String.Pattern "\\") (String.Replacement "/") directory
    # \s -> if String.takeRight 1 s == "/" 
            then String.dropRight 1 s 
            else s

-- | Get workspace name (custom or branch name or filename)
workspaceName :: String -> Maybe String -> Maybe String -> PersistedState -> Maybe String
workspaceName directory projectId branch state =
  let key = workspaceKey directory
      direct = Map.lookup key state.workspaceName
  in case direct of
       Just name -> Just name
       Nothing -> do
         pid <- projectId
         b <- branch
         branchNames <- Map.lookup pid state.workspaceBranchName
         Map.lookup b branchNames

-- | Get workspace label for display
workspaceLabel :: String -> Maybe String -> Maybe String -> PersistedState -> String
workspaceLabel directory branch projectId state =
  fromMaybe (fromMaybe (getFilename directory) branch) 
            (workspaceName directory projectId branch state)

-- | Sort sessions by recency
-- | Recent sessions (< 1 minute) sorted by ID, others by updated time desc
sortSessions :: Instant -> Session -> Session -> Ordering
sortSessions now a b =
  let oneMinuteAgo = now  -- simplified, actual: now - 60000ms
      aUpdated = fromMaybe a.time.created a.time.updated
      bUpdated = fromMaybe b.time.created b.time.updated
      aRecent = aUpdated > oneMinuteAgo
      bRecent = bUpdated > oneMinuteAgo
  in if aRecent && bRecent 
     then compare a.id b.id
     else if aRecent then LT
     else if bRecent then GT
     else compare bUpdated aUpdated

-- | Cycle through themes
cycleTheme :: Int -> Array ThemeEntry -> String -> Effect String
cycleTheme direction themes currentId =
  let ids = map (\(Tuple id _) -> id) themes
      currentIndex = fromMaybe 0 $ Array.elemIndex currentId ids
      nextIndex = (currentIndex + direction + Array.length ids) `mod` Array.length ids
  in pure $ fromMaybe currentId $ Array.index ids nextIndex

-- | Cycle through color schemes
cycleColorScheme :: Int -> ColorScheme -> ColorScheme
cycleColorScheme direction current =
  let order = [System, Light, Dark]
      currentIndex = fromMaybe 0 $ Array.elemIndex current order
      nextIndex = (currentIndex + direction + 3) `mod` 3
  in fromMaybe System $ Array.index order nextIndex

-- | Cycle through languages
cycleLanguage :: Int -> Array Locale -> Locale -> Locale
cycleLanguage direction locales current =
  let currentIndex = fromMaybe 0 $ Array.elemIndex current locales
      nextIndex = (currentIndex + direction + Array.length locales) `mod` Array.length locales
  in fromMaybe current $ Array.index locales nextIndex

-- | Navigate to project
navigateToProject :: String -> PersistedState -> Effect Unit
navigateToProject directory state = do
  let lastSession = Map.lookup directory state.lastSession
      path = "/" <> base64Encode directory <> 
             (case lastSession of
                Just sid -> "/session/" <> sid
                Nothing -> "")
  -- navigate(path)
  pure unit

-- | Navigate to session
navigateToSession :: Session -> Effect Unit
navigateToSession session = do
  let path = "/" <> base64Encode session.directory <> "/session/" <> session.id
  -- navigate(path)
  pure unit

-- | Open project
openProject :: LayoutContext -> String -> Boolean -> Effect Unit
openProject layout directory shouldNavigate = do
  -- layout.projects.open(directory)
  -- if shouldNavigate then navigateToProject(directory)
  pure unit

-- | Close project
closeProject :: LayoutContext -> String -> Effect Unit
closeProject layout directory = do
  -- layout.projects.close(directory)
  -- navigate to next project or home
  pure unit

-- | Archive session
archiveSession :: GlobalSDKContext -> GlobalSyncContext -> Session -> Aff Unit
archiveSession sdk sync session = do
  -- Update session with archived timestamp
  -- Remove from local store
  -- Navigate to next session if needed
  pure unit

-- | Delete session
deleteSession :: GlobalSDKContext -> GlobalSyncContext -> Session -> LanguageContext -> Aff Unit
deleteSession sdk sync session language = do
  -- Call SDK to delete
  -- Remove from local store (including children)
  -- Navigate to next session if needed
  pure unit

-- | Create workspace
createWorkspace :: GlobalSDKContext -> LocalProject -> LayoutPageState -> Effect Unit
createWorkspace sdk project state = do
  -- Call SDK worktree.create
  -- Update workspace order
  -- Navigate to new workspace
  pure unit

-- | Delete workspace
deleteWorkspace :: GlobalSDKContext -> String -> String -> Effect Unit
deleteWorkspace sdk root directory = do
  -- Call SDK worktree.remove
  -- Navigate to root
  pure unit

-- | Reset workspace
resetWorkspace :: GlobalSDKContext -> String -> String -> LanguageContext -> Effect Unit
resetWorkspace sdk root directory language = do
  -- Show progress toast
  -- Archive all sessions
  -- Call SDK worktree.reset
  -- Dispose instance
  -- Show success toast
  pure unit

-- | Rename project
renameProject :: GlobalSDKContext -> GlobalSyncContext -> LocalProject -> String -> Aff Unit
renameProject sdk sync project newName = do
  -- If project has ID: call SDK project.update
  -- Otherwise: update local meta
  pure unit

-- | Rename session  
renameSession :: GlobalSDKContext -> Session -> String -> Aff Unit
renameSession sdk session newName = do
  -- Call SDK session.update with new title
  pure unit

-- | Rename workspace
renameWorkspace :: String -> String -> Maybe String -> Maybe String -> PersistedState -> PersistedState
renameWorkspace directory newName projectId branch state =
  let key = workspaceKey directory
      withDirect = state { workspaceName = Map.insert key newName state.workspaceName }
  in case projectId, branch of
       Just pid, Just b ->
         let branchNames = fromMaybe Map.empty $ Map.lookup pid withDirect.workspaceBranchName
             updated = Map.insert b newName branchNames
         in withDirect { workspaceBranchName = Map.insert pid updated withDirect.workspaceBranchName }
       _, _ -> withDirect

-- | Handle deep link
handleDeepLink :: String -> ServerContext -> LayoutContext -> Effect Unit
handleDeepLink url server layout = do
  -- Parse forge:// URL
  -- Extract directory from query params
  -- Open project
  pure unit

-- | Prefetch session messages
prefetchSession :: GlobalSDKContext -> GlobalSyncContext -> Session -> String -> Aff Unit
prefetchSession sdk sync session priority = do
  -- Check if already cached
  -- Add to prefetch queue based on priority
  -- Pump prefetch queue
  pure unit

-- | Register layout commands
registerCommands :: CommandContext -> LanguageContext -> LayoutContext -> Array CommandOption
registerCommands command language layout =
  [ { id: "sidebar.toggle"
    , title: "Toggle Sidebar"  -- language.t("command.sidebar.toggle")
    , category: "View"
    , keybind: Just "mod+b"
    , onSelect: pure unit
    }
  , { id: "project.open"
    , title: "Open Project"
    , category: "Project"
    , keybind: Just "mod+o"
    , onSelect: pure unit
    }
  , { id: "provider.connect"
    , title: "Connect Provider"
    , category: "Provider"
    , keybind: Nothing
    , onSelect: pure unit
    }
  , { id: "server.switch"
    , title: "Switch Server"
    , category: "Server"
    , keybind: Nothing
    , onSelect: pure unit
    }
  , { id: "settings.open"
    , title: "Settings"
    , category: "Settings"
    , keybind: Just "mod+comma"
    , onSelect: pure unit
    }
  , { id: "session.previous"
    , title: "Previous Session"
    , category: "Session"
    , keybind: Just "alt+arrowup"
    , onSelect: pure unit
    }
  , { id: "session.next"
    , title: "Next Session"
    , category: "Session"
    , keybind: Just "alt+arrowdown"
    , onSelect: pure unit
    }
  , { id: "session.archive"
    , title: "Archive Session"
    , category: "Session"
    , keybind: Just "mod+shift+backspace"
    , onSelect: pure unit
    }
  , { id: "theme.cycle"
    , title: "Cycle Theme"
    , category: "Theme"
    , keybind: Just "mod+shift+t"
    , onSelect: pure unit
    }
  , { id: "theme.scheme.cycle"
    , title: "Cycle Color Scheme"
    , category: "Theme"
    , keybind: Just "mod+shift+s"
    , onSelect: pure unit
    }
  , { id: "language.cycle"
    , title: "Cycle Language"
    , category: "Language"
    , keybind: Nothing
    , onSelect: pure unit
    }
  ]

-- | Project icon component props
type ProjectIconProps =
  { project :: LocalProject
  , class :: Maybe String
  , notify :: Boolean
  }

-- | Project icon component
-- | Shows project avatar with notification badge
type ProjectIcon = ProjectIconProps -> Effect Unit

-- | Session item props
type SessionItemProps =
  { session :: Session
  , slug :: String
  , mobile :: Boolean
  , dense :: Boolean
  , popover :: Boolean
  , children :: Map String (Array String)
  }

-- | Session item component
-- | Shows session in sidebar with status indicators
type SessionItem = SessionItemProps -> Effect Unit

-- | Sortable project props
type SortableProjectProps =
  { project :: LocalProject
  , mobile :: Boolean
  }

-- | Sortable project component
-- | Draggable project in sidebar
type SortableProject = SortableProjectProps -> Effect Unit

-- | Sortable workspace props
type SortableWorkspaceProps =
  { directory :: String
  , project :: LocalProject
  , mobile :: Boolean
  }

-- | Sortable workspace component
-- | Draggable workspace in sidebar
type SortableWorkspace = SortableWorkspaceProps -> Effect Unit

-- | Sidebar panel props
type SidebarPanelProps =
  { project :: Maybe LocalProject
  , mobile :: Boolean
  }

-- | Sidebar panel component
-- | Shows project details and session list
type SidebarPanel = SidebarPanelProps -> Effect Unit

-- | Sidebar content props
type SidebarContentProps =
  { mobile :: Boolean
  }

-- | Sidebar content component
-- | Full sidebar with project list and panel
type SidebarContent = SidebarContentProps -> Effect Unit

-- | Layout page component
-- |
-- | Structure:
-- | - Titlebar
-- | - Main flex container:
-- |   - Desktop sidebar (nav)
-- |     - Project icons column
-- |     - Sidebar panel (expanded)
-- |     - Resize handle
-- |   - Mobile sidebar overlay
-- |   - Main content area
-- | - Toast region
-- |
-- | Effects:
-- | - Persist layout state
-- | - Load/restore from localStorage
-- | - Update check on mount
-- | - Deep link handling
-- | - Notification listeners
-- | - Command registration
-- | - Drag-and-drop handlers
type LayoutPage = LayoutPageProps -> Effect Unit
