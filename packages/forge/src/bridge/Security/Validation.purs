-- | Input Validation - Request Input Validation and Sanitization
module Bridge.Security.Validation where

import Prelude
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Bridge.Error.Taxonomy (BridgeError, ErrorCategory(..), RecoveryStrategy(..), createError)

-- | FFI declarations (top-level)
foreign import matchesPattern :: String -> String -> Boolean
foreign import stringLength :: String -> Int
foreign import isInteger :: Number -> Boolean
foreign import sanitizeImpl :: String -> String
foreign import isValidJson :: String -> Boolean
foreign import isValidEmail :: String -> Boolean
foreign import isValidUrl :: String -> Boolean

-- | String validation options
type StringValidationOptions =
  { minLength :: Maybe Int
  , maxLength :: Maybe Int
  , pattern :: Maybe String
  , allowEmpty :: Boolean
  }

-- | Number validation options
type NumberValidationOptions =
  { min :: Maybe Number
  , max :: Maybe Number
  , integer :: Boolean
  }

-- | Create a validation error
createValidationError :: String -> String -> BridgeError
createValidationError message details =
  createError ValidationError 4004 message message false FixAndRetry (Just details)

-- | Validate string
validateString :: String -> StringValidationOptions -> Either BridgeError String
validateString value options =
  if not options.allowEmpty && value == "" then
    Left (createValidationError "Value is required" "Empty string not allowed")
  else case options.minLength of
    Just minLen ->
      if stringLength value < minLen then
        Left (createValidationError "String too short" ("Minimum length: " <> show minLen))
      else validateMaxLength value options
    Nothing -> validateMaxLength value options

-- | Validate max length (internal helper)
validateMaxLength :: String -> StringValidationOptions -> Either BridgeError String
validateMaxLength value options =
  case options.maxLength of
    Just maxLen ->
      if stringLength value > maxLen then
        Left (createValidationError "String too long" ("Maximum length: " <> show maxLen))
      else validatePattern value options
    Nothing -> validatePattern value options

-- | Validate pattern (internal helper)
validatePattern :: String -> StringValidationOptions -> Either BridgeError String
validatePattern value options =
  case options.pattern of
    Just pat ->
      if matchesPattern value pat then Right value
      else Left (createValidationError "String does not match pattern" pat)
    Nothing -> Right value

-- | Validate number
validateNumber :: Number -> NumberValidationOptions -> Either BridgeError Number
validateNumber value options =
  if options.integer && not (isInteger value) then
    Left (createValidationError "Number must be integer" (show value))
  else case options.min of
    Just minVal ->
      if value < minVal then
        Left (createValidationError "Number too small" ("Minimum: " <> show minVal))
      else validateMax value options
    Nothing -> validateMax value options

-- | Validate max (internal helper)
validateMax :: Number -> NumberValidationOptions -> Either BridgeError Number
validateMax value options =
  case options.max of
    Just maxVal ->
      if value > maxVal then
        Left (createValidationError "Number too large" ("Maximum: " <> show maxVal))
      else Right value
    Nothing -> Right value

-- | Sanitize string to remove dangerous characters
sanitizeString :: String -> String
sanitizeString = sanitizeImpl

-- | Validate JSON format
validateJson :: String -> String -> Either BridgeError String
validateJson json _schema =
  if isValidJson json then Right json
  else Left (createValidationError "Invalid JSON format" json)

-- | Validate email format
validateEmail :: String -> Either BridgeError String
validateEmail email =
  if isValidEmail email then Right email
  else Left (createValidationError "Invalid email format" email)

-- | Validate URL format
validateUrl :: String -> Either BridgeError String
validateUrl url =
  if isValidUrl url then Right url
  else Left (createValidationError "Invalid URL format" url)
