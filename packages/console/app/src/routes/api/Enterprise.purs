-- | Enterprise API Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/api/enterprise.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Api.Enterprise
  ( EnterpriseFormData(..)
  , EnterpriseResponse(..)
  , ValidationError(..)
  , validateFormData
  , buildEmailContent
  , buildEmailRequest
  , handlePost
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (null, trim)
import Data.String.Regex (Regex, test)
import Data.String.Regex.Flags (noFlags)
import Data.String.Regex.Unsafe (unsafeRegex)

-- | Enterprise form data
type EnterpriseFormData =
  { name :: String
  , role :: String
  , email :: String
  , message :: String
  }

-- | Validation errors
data ValidationError
  = MissingName
  | MissingRole
  | MissingEmail
  | MissingMessage
  | InvalidEmailFormat

derive instance eqValidationError :: Eq ValidationError

instance showValidationError :: Show ValidationError where
  show MissingName = "Name is required"
  show MissingRole = "Role is required"
  show MissingEmail = "Email is required"
  show MissingMessage = "Message is required"
  show InvalidEmailFormat = "Invalid email format"

-- | API response types
data EnterpriseResponse
  = SuccessResponse { message :: String }
  | ErrorResponse { error :: String, status :: Int }

derive instance eqEnterpriseResponse :: Eq EnterpriseResponse

instance showEnterpriseResponse :: Show EnterpriseResponse where
  show (SuccessResponse r) = "(SuccessResponse " <> show r.message <> ")"
  show (ErrorResponse r) = "(ErrorResponse " <> show r.error <> " " <> show r.status <> ")"

-- | Email regex pattern
emailRegex :: Regex
emailRegex = unsafeRegex "^[^\\s@]+@[^\\s@]+\\.[^\\s@]+$" noFlags

-- | Validate email format
validateEmail :: String -> Boolean
validateEmail = test emailRegex

-- | Validate form data (pure)
validateFormData :: EnterpriseFormData -> Either ValidationError EnterpriseFormData
validateFormData form
  | null (trim form.name) = Left MissingName
  | null (trim form.role) = Left MissingRole
  | null (trim form.email) = Left MissingEmail
  | null (trim form.message) = Left MissingMessage
  | not (validateEmail form.email) = Left InvalidEmailFormat
  | otherwise = Right form

-- | Build email content from form data (pure)
buildEmailContent :: EnterpriseFormData -> String
buildEmailContent form =
  form.message <> "<br><br>\n--<br>\n" <>
  form.name <> "<br>\n" <>
  form.role <> "<br>\n" <>
  form.email

-- | Email request configuration (pure data)
type EmailRequest =
  { to :: String
  , subject :: String
  , body :: String
  , replyTo :: String
  }

-- | Build email request (pure)
buildEmailRequest :: EnterpriseFormData -> EmailRequest
buildEmailRequest form =
  { to: "contact@anoma.ly"
  , subject: "Enterprise Inquiry from " <> form.name
  , body: buildEmailContent form
  , replyTo: form.email
  }

-- | Handle POST request (pure logic)
handlePost :: EnterpriseFormData -> Either ValidationError EmailRequest
handlePost form = do
  validated <- validateFormData form
  pure (buildEmailRequest validated)

-- | Success response
successResponse :: EnterpriseResponse
successResponse = SuccessResponse { message: "Form submitted successfully" }

-- | Error response builder
errorResponse :: ValidationError -> EnterpriseResponse
errorResponse err = ErrorResponse { error: show err, status: 400 }

-- | Internal error response
internalErrorResponse :: String -> EnterpriseResponse
internalErrorResponse msg = ErrorResponse { error: msg, status: 500 }
