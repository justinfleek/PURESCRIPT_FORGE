-- | Email Signup Component
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/component/email-signup.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Component.EmailSignup
  ( EmailSignupState(..)
  , EmailSignupAction(..)
  , SubmissionStatus(..)
  , EmailAddress
  , ListId
  , mkEmailAddress
  , mkListId
  , defaultListId
  , initialState
  , reducer
  , validateEmail
  , signupRequest
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.Regex (Regex, test)
import Data.String.Regex.Flags (noFlags)
import Data.String.Regex.Unsafe (unsafeRegex)

-- | Email address validated wrapper
newtype EmailAddress = EmailAddress String

derive instance eqEmailAddress :: Eq EmailAddress
derive instance ordEmailAddress :: Ord EmailAddress

instance showEmailAddress :: Show EmailAddress where
  show (EmailAddress e) = "(EmailAddress " <> show e <> ")"

-- | List ID for email service
newtype ListId = ListId String

derive instance eqListId :: Eq ListId
derive instance ordListId :: Ord ListId

instance showListId :: Show ListId where
  show (ListId l) = "(ListId " <> show l <> ")"

-- | Smart constructor for email address with validation
mkEmailAddress :: String -> Either String EmailAddress
mkEmailAddress email
  | String.null (String.trim email) = Left "Email address is required"
  | not (validateEmailFormat email) = Left "Invalid email format"
  | otherwise = Right (EmailAddress (String.trim email))

-- | Validate email format using regex
validateEmailFormat :: String -> Boolean
validateEmailFormat = test emailRegex
  where
    emailRegex :: Regex
    emailRegex = unsafeRegex "^[^\\s@]+@[^\\s@]+\\.[^\\s@]+$" noFlags

-- | Smart constructor for list ID
mkListId :: String -> Maybe ListId
mkListId id
  | String.null (String.trim id) = Nothing
  | otherwise = Just (ListId (String.trim id))

-- | Default EmailOctopus list ID from source
defaultListId :: ListId
defaultListId = ListId "8b9bb82c-9d5f-11f0-975f-0df6fd1e4945"

-- | Submission status ADT
data SubmissionStatus
  = Idle
  | Pending
  | Success
  | Error String

derive instance eqSubmissionStatus :: Eq SubmissionStatus

instance showSubmissionStatus :: Show SubmissionStatus where
  show Idle = "Idle"
  show Pending = "Pending"
  show Success = "Success"
  show (Error msg) = "(Error " <> show msg <> ")"

-- | Component state
type EmailSignupState =
  { emailInput :: String
  , status :: SubmissionStatus
  , listId :: ListId
  }

-- | Initial state
initialState :: EmailSignupState
initialState =
  { emailInput: ""
  , status: Idle
  , listId: defaultListId
  }

-- | Component actions
data EmailSignupAction
  = SetEmail String
  | Submit
  | SubmitSuccess
  | SubmitError String
  | Reset

derive instance eqEmailSignupAction :: Eq EmailSignupAction

instance showEmailSignupAction :: Show EmailSignupAction where
  show (SetEmail e) = "(SetEmail " <> show e <> ")"
  show Submit = "Submit"
  show SubmitSuccess = "SubmitSuccess"
  show (SubmitError e) = "(SubmitError " <> show e <> ")"
  show Reset = "Reset"

-- | Pure state reducer
reducer :: EmailSignupState -> EmailSignupAction -> EmailSignupState
reducer state action = case action of
  SetEmail email ->
    state { emailInput = email, status = Idle }
  
  Submit ->
    state { status = Pending }
  
  SubmitSuccess ->
    state { status = Success, emailInput = "" }
  
  SubmitError msg ->
    state { status = Error msg }
  
  Reset ->
    initialState

-- | Validate email for submission (pure)
validateEmail :: EmailSignupState -> Either String EmailAddress
validateEmail state = mkEmailAddress state.emailInput

-- | Request configuration for email signup
-- | This represents the API call structure, not the actual HTTP call
type SignupRequest =
  { url :: String
  , method :: String
  , headers :: Array { name :: String, value :: String }
  , body :: { email_address :: String }
  }

-- | Build signup request (pure function)
signupRequest :: ListId -> EmailAddress -> String -> SignupRequest
signupRequest (ListId listId) (EmailAddress email) apiKey =
  { url: "https://api.emailoctopus.com/lists/" <> listId <> "/contacts"
  , method: "PUT"
  , headers:
      [ { name: "Authorization", value: "Bearer " <> apiKey }
      , { name: "Content-Type", value: "application/json" }
      ]
  , body: { email_address: email }
  }

-- | UI Text (i18n ready)
type UIText =
  { title :: String
  , subtitle :: String
  , placeholder :: String
  , buttonText :: String
  , successMessage :: String
  }

defaultUIText :: UIText
defaultUIText =
  { title: "Be the first to know when we release new products"
  , subtitle: "Join the waitlist for early access."
  , placeholder: "Email address"
  , buttonText: "Subscribe"
  , successMessage: "Almost done, check your inbox and confirm your email address"
  }
