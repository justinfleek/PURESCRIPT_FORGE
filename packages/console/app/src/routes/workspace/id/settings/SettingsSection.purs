-- | Settings Section - Workspace Settings
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/settings/settings-section.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Settings.SettingsSection
  ( SettingsSectionState(..)
  , SettingsSectionAction(..)
  , WorkspaceInfo(..)
  , UpdateFormData(..)
  , initialState
  , reducer
  , validateWorkspaceName
  , buildFormData
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String as String

-- | Workspace info from database
type WorkspaceInfo =
  { id :: String
  , name :: String
  , slug :: String
  }

-- | Settings section state
type SettingsSectionState =
  { show :: Boolean
  }

-- | Actions for settings section
data SettingsSectionAction
  = Show
  | Hide

-- | Initial state
initialState :: SettingsSectionState
initialState =
  { show: false
  }

-- | Pure state reducer
reducer :: SettingsSectionState -> SettingsSectionAction -> SettingsSectionState
reducer state action = case action of
  Show -> state { show = true }
  Hide -> state { show = false }

-- | Form data for updating workspace
type UpdateFormData =
  { name :: String
  , workspaceId :: String
  }

-- | Build form data
buildFormData :: String -> String -> UpdateFormData
buildFormData name workspaceId =
  { name
  , workspaceId
  }

-- | Validation error
type ValidationError = String

-- | Max workspace name length
maxNameLength :: Int
maxNameLength = 255

-- | Validate workspace name
validateWorkspaceName :: String -> Maybe ValidationError
validateWorkspaceName name
  | String.trim name == "" = Just "Workspace name is required."
  | String.length name > maxNameLength = Just "Name must be 255 characters or less."
  | otherwise = Nothing

-- | Section content
type SettingsSectionContent =
  { title :: String
  , description :: String
  , workspaceNameLabel :: String
  , editButtonLabel :: String
  }

-- | Default section content
sectionContent :: SettingsSectionContent
sectionContent =
  { title: "Settings"
  , description: "Update your workspace name and preferences."
  , workspaceNameLabel: "Workspace name"
  , editButtonLabel: "Edit"
  }

-- | Button state
type ButtonState =
  { disabled :: Boolean
  , label :: String
  }

-- | Update button state
updateButtonState :: { pending :: Boolean } -> ButtonState
updateButtonState { pending } =
  { disabled: pending
  , label: if pending then "Updating..." else "Save"
  }

-- | Setting display
type SettingDisplay =
  { label :: String
  , value :: String
  , editing :: Boolean
  }

-- | Build setting display
buildSettingDisplay :: SettingsSectionState -> WorkspaceInfo -> SettingDisplay
buildSettingDisplay state workspaceInfo =
  { label: "Workspace name"
  , value: workspaceInfo.name
  , editing: state.show
  }

-- | Form state
type FormState =
  { visible :: Boolean
  , currentValue :: String
  , error :: Maybe String
  , pending :: Boolean
  }

-- | Build form state
buildFormState :: SettingsSectionState -> WorkspaceInfo -> Maybe String -> Boolean -> FormState
buildFormState state workspaceInfo error pending =
  { visible: state.show
  , currentValue: workspaceInfo.name
  , error
  , pending
  }

-- | Default workspace name
defaultWorkspaceName :: String
defaultWorkspaceName = "Default"

-- | Get display name (fallback to default if empty)
getDisplayName :: Maybe WorkspaceInfo -> String
getDisplayName mbInfo =
  case mbInfo of
    Nothing -> defaultWorkspaceName
    Just info -> 
      if info.name == ""
        then defaultWorkspaceName
        else info.name
