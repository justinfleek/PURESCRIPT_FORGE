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
import Bridge.Error.Taxonomy (BridgeError, ValidationError(..), MISSING_FIELD, VALUE_OUT_OF_RANGE, invalidJson, missingField, createError, FixAndRetry)

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
validateString value options = do
  -- Check empty
  if not options.allowEmpty && value == "" then
    Left (missingField "value")
  else
    pure ()
  
  -- Check min length
  case options.minLength of
    Just minLen -> if length value < minLen then
      Left (createValidationError "String too short" ("Minimum length: " <> show minLen))
    else
      pure ()
    Nothing -> pure ()
  
  -- Check max length
  case options.maxLength of
    Just maxLen -> if length value > maxLen then
      Left (createValidationError "String too long" ("Maximum length: " <> show maxLen))
    else
      pure ()
    Nothing -> pure ()
  
  -- Check pattern
  case options.pattern of
    Just pattern -> if matchesPattern value pattern then
      pure value
    else
      Left (createValidationError "String does not match pattern" pattern)
    Nothing -> pure value
  where
    foreign import matchesPattern :: String -> String -> Boolean
    foreign import length :: String -> Int
    
    createValidationError :: String -> String -> BridgeError
    createValidationError message details =
      createError ValidationError VALUE_OUT_OF_RANGE message message false FixAndRetry (Just details)

-- | Validate number
-- |
-- | **Purpose:** Validates a number input against constraints.
-- | **Parameters:**
-- | - `value`: Number to validate
-- | - `options`: Validation options
-- | **Returns:** Either error or validated number
validateNumber :: Number -> NumberValidationOptions -> Either BridgeError Number
validateNumber value options = do
  -- Check if integer required
  if options.integer && not (isInteger value) then
    Left (createValidationError "Number must be integer" (show value))
  else
    pure ()
  
  -- Check min
  case options.min of
    Just minVal -> if value < minVal then
      Left (createValidationError "Number too small" ("Minimum: " <> show minVal))
    else
      pure ()
    Nothing -> pure ()
  
  -- Check max
  case options.max of
    Just maxVal -> if value > maxVal then
      Left (createValidationError "Number too large" ("Maximum: " <> show maxVal))
    else
      pure value
    Nothing -> pure value
  where
    foreign import isInteger :: Number -> Boolean
    
    createValidationError :: String -> String -> BridgeError
    createValidationError message details =
      createError ValidationError VALUE_OUT_OF_RANGE message message false FixAndRetry (Just details)

-- | Sanitize string
-- |
-- | **Purpose:** Sanitizes a string to remove potentially dangerous characters.
-- | **Parameters:**
-- | - `value`: String to sanitize
-- | **Returns:** Sanitized string
sanitizeString :: String -> String
sanitizeString value = do
  sanitizeImpl value
  where
    foreign import sanitizeImpl :: String -> String

-- | Validate JSON
-- |
-- | **Purpose:** Validates JSON input structure.
-- | **Parameters:**
-- | - `json`: JSON string
-- | - `schema`: JSON schema (simplified - would use JSON Schema in production)
-- | **Returns:** Either error or validated JSON
validateJson :: String -> String -> Either BridgeError String
validateJson json schema = do
  if isValidJson json then
    Right json
  else
    Left (invalidJson "Invalid JSON format")
  where
    foreign import isValidJson :: String -> Boolean

-- | Validate email
-- |
-- | **Purpose:** Validates email address format.
-- | **Parameters:**
-- | - `email`: Email string
-- | **Returns:** Either error or validated email
validateEmail :: String -> Either BridgeError String
validateEmail email = do
  if isValidEmail email then
    Right email
  else
    Left (createValidationError "Invalid email format" email)
  where
    foreign import isValidEmail :: String -> Boolean
    
    createValidationError :: String -> String -> BridgeError
    createValidationError message details =
      createError ValidationError VALUE_OUT_OF_RANGE message message false FixAndRetry (Just details)

-- | Validate URL
-- |
-- | **Purpose:** Validates URL format.
-- | **Parameters:**
-- | - `url`: URL string
-- | **Returns:** Either error or validated URL
validateUrl :: String -> Either BridgeError String
validateUrl url = do
  if isValidUrl url then
    Right url
  else
    Left (createValidationError "Invalid URL format" url)
  where
    foreign import isValidUrl :: String -> Boolean
    
    createValidationError :: String -> String -> BridgeError
    createValidationError message details =
      createError ValidationError VALUE_OUT_OF_RANGE message message false FixAndRetry (Just details)
