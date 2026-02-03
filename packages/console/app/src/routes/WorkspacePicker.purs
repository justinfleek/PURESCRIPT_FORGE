-- | Workspace Picker Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace-picker.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.WorkspacePicker
  ( WorkspaceItem(..)
  , WorkspacePickerState(..)
  , WorkspacePickerAction(..)
  , initialState
  , reducer
  , buildWorkspaceUrl
  ) where

import Prelude

import Data.Array (find)
import Data.Maybe (Maybe(..))

-- | Workspace item from query
type WorkspaceItem =
  { id :: String
  , name :: String
  , slug :: String
  }

-- | Workspace picker state
type WorkspacePickerState =
  { workspaces :: Array WorkspaceItem
  , currentId :: Maybe String
  , showForm :: Boolean
  , newWorkspaceName :: String
  , isCreating :: Boolean
  }

-- | Initial state
initialState :: Maybe String -> WorkspacePickerState
initialState currentId =
  { workspaces: []
  , currentId
  , showForm: false
  , newWorkspaceName: ""
  , isCreating: false
  }

-- | Actions
data WorkspacePickerAction
  = SetWorkspaces (Array WorkspaceItem)
  | SetCurrentId String
  | ShowCreateForm
  | HideCreateForm
  | SetNewWorkspaceName String
  | StartCreate
  | CreateSuccess String  -- new workspace ID
  | CreateError

derive instance eqWorkspacePickerAction :: Eq WorkspacePickerAction

-- | State reducer (pure)
reducer :: WorkspacePickerState -> WorkspacePickerAction -> WorkspacePickerState
reducer state action = case action of
  SetWorkspaces workspaces ->
    state { workspaces = workspaces }
  
  SetCurrentId id ->
    state { currentId = Just id, showForm = false }
  
  ShowCreateForm ->
    state { showForm = true }
  
  HideCreateForm ->
    state { showForm = false, newWorkspaceName = "" }
  
  SetNewWorkspaceName name ->
    state { newWorkspaceName = name }
  
  StartCreate ->
    state { isCreating = true }
  
  CreateSuccess newId ->
    state { isCreating = false, showForm = false, currentId = Just newId, newWorkspaceName = "" }
  
  CreateError ->
    state { isCreating = false }

-- | Get current workspace name
getCurrentWorkspaceName :: WorkspacePickerState -> String
getCurrentWorkspaceName state = case state.currentId of
  Nothing -> "Select workspace"
  Just id -> case find (\w -> w.id == id) state.workspaces of
    Just ws -> if ws.name == "" then ws.slug else ws.name
    Nothing -> "Select workspace"

-- | Build workspace URL
buildWorkspaceUrl :: String -> String
buildWorkspaceUrl workspaceId = "/workspace/" <> workspaceId
