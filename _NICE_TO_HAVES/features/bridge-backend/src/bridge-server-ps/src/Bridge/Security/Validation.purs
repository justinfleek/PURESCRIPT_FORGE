-- | Input Validation - Request Input Validation and Sanitization
-- |
-- | **What:** Validates and sanitizes all user inputs to prevent injection attacks,
-- |         XSS, and other security vulnerabilities. Provides type-safe validation.
-- | **Why:** Prevents security vulnerabilities from malicious input. Ensures data
-- |         integrity and prevents injection attacks.
-- | **How:** Validates input types, ranges, formats. Sanitizes strings. Rejects
-- |         invalid input with clear error messages.
-- |
-- | **Dependencies:**
-- | - `Bridge.Error.Taxonomy`: Error types
-- |
-- | **Mathematical Foundation:**
-- | - **Validation:** `isValid(input) -> Boolean`
-- | - **Sanitization:** `sanitize(input) -> safeInput`
-- | - **Type Safety:** Input types enforced at compile time
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Security.Validation as Validation
-- |
-- | -- Validate string
-- | result <- Validation.validateString input { minLength: 1, maxLength: 100 }
-- | case result of
-- |   Right valid -> -- Use valid input
-- |   Left err -> -- Handle validation error
-- | ```
module Bridge.Security.Validation where

import Prelude
import Effect (Effect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Bridge.Error.Taxonomy (BridgeError, ErrorCategory(..), RecoveryStrategy(..), valueOutOfRangeCode, invalidJson, missingField, createError)

-- | FFI: Check if string matches pattern
foreign import matchesPattern :: String -> String -> Boolean

-- | FFI: Get string length
foreign import length :: String -> Int

-- | FFI: Check if number is integer
foreign import isInteger :: Number -> Boolean

-- | FFI: Sanitize string
foreign import sanitizeImpl :: String -> String

-- | FFI: Check if JSON is valid
foreign import isValidJson :: String -> Boolean

-- | FFI: Check if email is valid
foreign import isValidEmail :: String -> Boolean

-- | FFI: Check if URL is valid
foreign import isValidUrl :: String -> Boolean

-- | Create validation error helper
createValidationError :: String -> String -> BridgeError
createValidationError message details =
  createError ValidationError valueOutOfRangeCode message message false FixAndRetry (Just details)

-- | String validation options
type StringValidationOptions =
  { minLength :: Maybe Int
  , maxLength :: Maybe Int
  , pattern :: Maybe String -- Regex pattern
  , allowEmpty :: Boolean
  }

-- | Number validation options
type NumberValidationOptions =
  { min :: Maybe Number
  , max :: Maybe Number
  , integer :: Boolean
  }

-- | Validate string
-- |
-- | **Purpose:** Validates a string input against constraints.
-- | **Parameters:**
-- | - `value`: String to validate
-- | - `options`: Validation options
-- | **Returns:** Either error or validated string
validateString :: String -> StringValidationOptions -> Either BridgeError String
validateString value options =
  -- Check empty
  if not options.allowEmpty && value == "" then
    Left (missingField "value")
  -- Check min length
  else case options.minLength of
    Just minLen | length value < minLen ->
      Left (createValidationError "String too short" ("Minimum length: " <> show minLen))
    _ ->
      -- Check max length
      case options.maxLength of
        Just maxLen | length value > maxLen ->
          Left (createValidationError "String too long" ("Maximum length: " <> show maxLen))
        _ ->
          -- Check pattern
          case options.pattern of
            Just pat -> if matchesPattern value pat then
              Right value
            else
              Left (createValidationError "String does not match pattern" pat)
            Nothing -> Right value

-- | Validate number
-- |
-- | **Purpose:** Validates a number input against constraints.
-- | **Parameters:**
-- | - `value`: Number to validate
-- | - `options`: Validation options
-- | **Returns:** Either error or validated number
validateNumber :: Number -> NumberValidationOptions -> Either BridgeError Number
validateNumber value options =
  -- Check if integer required
  if options.integer && not (isInteger value) then
    Left (createValidationError "Number must be integer" (show value))
  -- Check min
  else case options.min of
    Just minVal | value < minVal ->
      Left (createValidationError "Number too small" ("Minimum: " <> show minVal))
    _ ->
      -- Check max
      case options.max of
        Just maxVal | value > maxVal ->
          Left (createValidationError "Number too large" ("Maximum: " <> show maxVal))
        _ -> Right value

-- | Sanitize string
-- |
-- | **Purpose:** Sanitizes a string to remove potentially dangerous characters.
-- | **Parameters:**
-- | - `value`: String to sanitize
-- | **Returns:** Sanitized string
sanitizeString :: String -> String
sanitizeString = sanitizeImpl

-- | Validate JSON
-- |
-- | **Purpose:** Validates JSON input structure.
-- | **Parameters:**
-- | - `json`: JSON string
-- | - `schema`: JSON schema (simplified - would use JSON Schema in production)
-- | **Returns:** Either error or validated JSON
validateJson :: String -> String -> Either BridgeError String
validateJson json _schema =
  if isValidJson json then
    Right json
  else
    Left (invalidJson "Invalid JSON format")

-- | Validate email
-- |
-- | **Purpose:** Validates email address format.
-- | **Parameters:**
-- | - `email`: Email string
-- | **Returns:** Either error or validated email
validateEmail :: String -> Either BridgeError String
validateEmail email =
  if isValidEmail email then
    Right email
  else
    Left (createValidationError "Invalid email format" email)

-- | Validate URL
-- |
-- | **Purpose:** Validates URL format.
-- | **Parameters:**
-- | - `url`: URL string
-- | **Returns:** Either error or validated URL
validateUrl :: String -> Either BridgeError String
validateUrl url =
  if isValidUrl url then
    Right url
  else
    Left (createValidationError "Invalid URL format" url)
