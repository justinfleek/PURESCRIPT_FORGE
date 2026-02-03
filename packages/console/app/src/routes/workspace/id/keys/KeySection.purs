-- | Key Section - API Key Management
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/keys/key-section.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Keys.KeySection
  ( KeySectionState(..)
  , KeySectionAction(..)
  , KeyRecord(..)
  , KeyFormData(..)
  , KeyDisplay(..)
  , initialState
  , reducer
  , validateKeyName
  , maskKeyValue
  , buildFormData
  , hasKeys
  ) where

import Prelude

import Data.Array (length)
import Data.Maybe (Maybe(..))
import Data.String (take, drop)
import Data.String as String

-- | Key record from database
type KeyRecord =
  { id :: String
  , name :: String
  , key :: Maybe String        -- Full key (only present on creation)
  , keyDisplay :: String       -- Masked key for display
  , email :: String            -- Creator's email
  , timeUsed :: Maybe String   -- Last used timestamp
  }

-- | Key display with copy state
type KeyDisplay =
  { id :: String
  , name :: String
  , keyDisplay :: String
  , fullKey :: Maybe String
  , email :: String
  , lastUsed :: String
  , lastUsedTitle :: Maybe String
  , canCopy :: Boolean
  }

-- | Key section state
type KeySectionState =
  { show :: Boolean
  }

-- | Actions for key section
data KeySectionAction
  = Show
  | Hide

-- | Initial state
initialState :: KeySectionState
initialState =
  { show: false
  }

-- | Pure state reducer
reducer :: KeySectionState -> KeySectionAction -> KeySectionState
reducer state action = case action of
  Show -> state { show = true }
  Hide -> state { show = false }

-- | Form data for key creation
type KeyFormData =
  { name :: String
  , workspaceId :: String
  }

-- | Build form data
buildFormData :: String -> String -> KeyFormData
buildFormData name workspaceId =
  { name
  , workspaceId
  }

-- | Validation error
type ValidationError = String

-- | Validate key name
validateKeyName :: String -> Maybe ValidationError
validateKeyName name
  | String.trim name == "" = Just "Name is required"
  | otherwise = Nothing

-- | Mask a key value for display
-- | Shows first 8 and last 4 characters
-- | Example: "sk-abc123...xyz9" -> "sk-abc12...xyz9"
maskKeyValue :: String -> String
maskKeyValue key =
  let
    len = String.length key
  in
    if len <= 12
      then key
      else take 8 key <> "..." <> drop (len - 4) key

-- | Build key display from record
buildKeyDisplay :: KeyRecord -> KeyDisplay
buildKeyDisplay key =
  { id: key.id
  , name: key.name
  , keyDisplay: key.keyDisplay
  , fullKey: key.key
  , email: key.email
  , lastUsed: case key.timeUsed of
      Nothing -> "-"
      Just t -> formatDateForTable t
  , lastUsedTitle: map formatDateUTC key.timeUsed
  , canCopy: case key.key of
      Nothing -> false
      Just _ -> true
  }

-- | Check if there are any keys
hasKeys :: Array KeyRecord -> Boolean
hasKeys keys = length keys > 0

-- | Format date for table display
formatDateForTable :: String -> String
formatDateForTable isoDate = isoDate  -- simplified

-- | Format date in UTC
formatDateUTC :: String -> String
formatDateUTC isoDate = isoDate  -- simplified

-- | Section content
type KeySectionContent =
  { title :: String
  , description :: String
  , createButtonLabel :: String
  , emptyMessage :: String
  }

-- | Default section content
sectionContent :: KeySectionContent
sectionContent =
  { title: "API Keys"
  , description: "Manage your API keys for accessing opencode services."
  , createButtonLabel: "Create API Key"
  , emptyMessage: "Create an opencode Gateway API key"
  }

-- | Table headers
type TableHeaders =
  { name :: String
  , key :: String
  , createdBy :: String
  , lastUsed :: String
  , actions :: String
  }

-- | Default table headers
tableHeaders :: TableHeaders
tableHeaders =
  { name: "Name"
  , key: "Key"
  , createdBy: "Created By"
  , lastUsed: "Last Used"
  , actions: ""
  }

-- | Button state
type ButtonState =
  { disabled :: Boolean
  , label :: String
  }

-- | Create button state
createButtonState :: { pending :: Boolean } -> ButtonState
createButtonState { pending } =
  { disabled: pending
  , label: if pending then "Creating..." else "Create"
  }

-- | Copy button state
type CopyButtonState =
  { disabled :: Boolean
  , copied :: Boolean
  }

-- | Build copy button state
buildCopyButtonState :: Boolean -> CopyButtonState
buildCopyButtonState copied =
  { disabled: copied
  , copied
  }

-- | Remove form data
type RemoveFormData =
  { id :: String
  , workspaceId :: String
  }

-- | Build remove form data
buildRemoveFormData :: String -> String -> RemoveFormData
buildRemoveFormData id workspaceId =
  { id
  , workspaceId
  }
