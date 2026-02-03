-- | Provider Section - BYOK (Bring Your Own Key)
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/provider-section.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.ProviderSection
  ( Provider(..)
  , ProviderKey(..)
  , ProviderInfo(..)
  , ProviderRowState(..)
  , ProviderRowAction(..)
  , ProviderFormData(..)
  , providers
  , maskCredentials
  , initialRowState
  , rowReducer
  , validateCredentials
  , buildFormData
  ) where

import Prelude

import Data.Array (filter)
import Data.Maybe (Maybe(..))
import Data.String (take, drop, length)

-- | Provider definition
type Provider =
  { name :: String
  , key :: String
  , prefix :: String
  }

-- | Available providers
providers :: Array Provider
providers =
  [ { name: "OpenAI", key: "openai", prefix: "sk-" }
  , { name: "Anthropic", key: "anthropic", prefix: "sk-ant-" }
  , { name: "Google Gemini", key: "google", prefix: "AI" }
  ]

-- | Provider key type (for type safety)
data ProviderKey
  = OpenAI
  | Anthropic
  | Google

derive instance eqProviderKey :: Eq ProviderKey

instance showProviderKey :: Show ProviderKey where
  show OpenAI = "openai"
  show Anthropic = "anthropic"
  show Google = "google"

-- | Parse provider key from string
parseProviderKey :: String -> Maybe ProviderKey
parseProviderKey s = case s of
  "openai" -> Just OpenAI
  "anthropic" -> Just Anthropic
  "google" -> Just Google
  _ -> Nothing

-- | Provider info from database
type ProviderInfo =
  { provider :: String
  , credentials :: String
  }

-- | Mask credentials for display
-- | Shows first 8 and last 8 characters
-- | Example: "sk-abc123xyz789" -> "sk-abc12...xyz789"
maskCredentials :: String -> String
maskCredentials credentials =
  let
    len = length credentials
  in
    if len <= 16
      then credentials
      else take 8 credentials <> "..." <> drop (len - 8) credentials

-- | Provider row state
type ProviderRowState =
  { editing :: Boolean
  }

-- | Provider row actions
data ProviderRowAction
  = StartEditing
  | StopEditing
  | ClearSubmission

-- | Initial row state
initialRowState :: ProviderRowState
initialRowState =
  { editing: false
  }

-- | Row state reducer
rowReducer :: ProviderRowState -> ProviderRowAction -> ProviderRowState
rowReducer state action = case action of
  StartEditing -> state { editing = true }
  StopEditing -> state { editing = false }
  ClearSubmission -> state

-- | Form data for provider operations
type ProviderFormData =
  { provider :: String
  , credentials :: String
  , workspaceId :: String
  }

-- | Build form data for save operation
buildFormData :: String -> String -> String -> ProviderFormData
buildFormData provider credentials workspaceId =
  { provider
  , credentials
  , workspaceId
  }

-- | Validation error
type ValidationError = String

-- | Validate credentials
validateCredentials :: String -> String -> Maybe ValidationError
validateCredentials provider credentials
  | credentials == "" = Just "API key is required"
  | otherwise = validatePrefix provider credentials

-- | Validate credentials prefix for provider
validatePrefix :: String -> String -> Maybe ValidationError
validatePrefix provider credentials =
  case findProvider provider of
    Nothing -> Just "Unknown provider"
    Just p ->
      if take (length p.prefix) credentials == p.prefix
        then Nothing
        else Just $ "API key should start with '" <> p.prefix <> "'"
  where
    findProvider :: String -> Maybe Provider
    findProvider key =
      case filter (\p -> p.key == key) providers of
        [p] -> Just p
        _ -> Nothing

-- | Form validation result
data FormValidation
  = Valid
  | Invalid ValidationError

-- | Validate form data
validateFormData :: ProviderFormData -> FormValidation
validateFormData formData
  | formData.provider == "" = Invalid "Provider is required"
  | formData.credentials == "" = Invalid "API key is required"
  | formData.workspaceId == "" = Invalid "Workspace ID is required"
  | otherwise = 
      case validateCredentials formData.provider formData.credentials of
        Just err -> Invalid err
        Nothing -> Valid

-- | Remove provider form data
type RemoveFormData =
  { provider :: String
  , workspaceId :: String
  }

-- | Build remove form data
buildRemoveFormData :: String -> String -> RemoveFormData
buildRemoveFormData provider workspaceId =
  { provider
  , workspaceId
  }

-- | Provider row display state
type ProviderRowDisplay =
  { name :: String
  , key :: String
  , prefix :: String
  , hasCredentials :: Boolean
  , maskedCredentials :: Maybe String
  , editing :: Boolean
  }

-- | Build provider row display
buildProviderRowDisplay :: Provider -> Maybe ProviderInfo -> ProviderRowState -> ProviderRowDisplay
buildProviderRowDisplay provider providerData state =
  { name: provider.name
  , key: provider.key
  , prefix: provider.prefix
  , hasCredentials: hasCredentials providerData
  , maskedCredentials: map (maskCredentials <<< _.credentials) providerData
  , editing: state.editing
  }
  where
    hasCredentials :: Maybe ProviderInfo -> Boolean
    hasCredentials Nothing = false
    hasCredentials (Just _) = true

-- | Action button state
data ActionButtonType
  = Configure
  | Edit
  | Delete
  | Save
  | Cancel

-- | Get action buttons for row
getActionButtons :: ProviderRowDisplay -> { pending :: Boolean } -> Array ActionButtonType
getActionButtons display submission
  | display.editing = 
      if submission.pending
        then [Save]
        else [Save, Cancel]
  | display.hasCredentials = [Edit, Delete]
  | otherwise = [Configure]

-- | Section content
type ProviderSectionContent =
  { title :: String
  , description :: String
  }

-- | Default section content
sectionContent :: ProviderSectionContent
sectionContent =
  { title: "Bring Your Own Key"
  , description: "Configure your own API keys from AI providers."
  }

-- | Table headers
type TableHeaders =
  { provider :: String
  , apiKey :: String
  , action :: String
  }

-- | Default table headers
tableHeaders :: TableHeaders
tableHeaders =
  { provider: "Provider"
  , apiKey: "API Key"
  , action: ""
  }

-- | Input placeholder builder
buildInputPlaceholder :: Provider -> String
buildInputPlaceholder provider =
  "Enter " <> provider.name <> " API key (" <> provider.prefix <> "...)"

-- | Submission state
type SubmissionState =
  { pending :: Boolean
  , result :: Maybe { error :: Maybe String }
  }

-- | Check if submission was successful
isSubmissionSuccess :: SubmissionState -> Boolean
isSubmissionSuccess state =
  case state.result of
    Nothing -> false
    Just { error: Nothing } -> true
    Just { error: Just _ } -> false

-- | Get submission error
getSubmissionError :: SubmissionState -> Maybe String
getSubmissionError state =
  case state.result of
    Nothing -> Nothing
    Just { error } -> error
