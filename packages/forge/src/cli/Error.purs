{-|
Module      : Forge.CLI.Error
Description : CLI Error handling

Structured error types and display utilities for CLI operations.
-}
module Forge.CLI.Error
  ( -- * Error Types
    CLIError(..)
  , ErrorCode(..)
    -- * Error Display
  , displayError
  , formatError
  , formatErrorWithCode
    -- * Error Creation
  , commandNotFound
  , invalidArgument
  , sessionError
  , networkError
  , configError
  , fileError
  , unknownError
  ) where

import Prelude

import Effect (Effect)

-- ============================================================================
-- FFI
-- ============================================================================

-- | Print error to stderr
foreign import printErrorFFI :: String -> Effect Unit

-- ============================================================================
-- ERROR TYPES
-- ============================================================================

-- | Error codes for programmatic handling
data ErrorCode
  = ErrCommandNotFound
  | ErrInvalidArgument
  | ErrSession
  | ErrNetwork
  | ErrConfig
  | ErrFile
  | ErrUnknown

derive instance eqErrorCode :: Eq ErrorCode

instance showErrorCode :: Show ErrorCode where
  show ErrCommandNotFound = "E001"
  show ErrInvalidArgument = "E002"
  show ErrSession = "E003"
  show ErrNetwork = "E004"
  show ErrConfig = "E005"
  show ErrFile = "E006"
  show ErrUnknown = "E999"

-- | Error types for CLI operations
data CLIError
  = CommandNotFound String
  | InvalidArgument String String  -- arg name, reason
  | SessionError String
  | NetworkError String
  | ConfigError String
  | FileError String String  -- path, reason
  | UnknownError String

derive instance eqCLIError :: Eq CLIError

-- ============================================================================
-- ERROR DISPLAY
-- ============================================================================

-- | Display a CLI error to the user (prints to stderr)
displayError :: CLIError -> Effect Unit
displayError err = printErrorFFI (formatErrorColored err)

-- | Format error for output (plain text)
formatError :: CLIError -> String
formatError (CommandNotFound cmd) = "Command not found: " <> cmd
formatError (InvalidArgument arg reason) = "Invalid argument '" <> arg <> "': " <> reason
formatError (SessionError msg) = "Session error: " <> msg
formatError (NetworkError msg) = "Network error: " <> msg
formatError (ConfigError msg) = "Configuration error: " <> msg
formatError (FileError path reason) = "File error (" <> path <> "): " <> reason
formatError (UnknownError msg) = "Error: " <> msg

-- | Format error with error code
formatErrorWithCode :: CLIError -> String
formatErrorWithCode err = 
  "[" <> show (getErrorCode err) <> "] " <> formatError err

-- | Format error with ANSI colors
formatErrorColored :: CLIError -> String
formatErrorColored err =
  "\x1b[31m" <>  -- Red
  "Error: " <>
  "\x1b[0m" <>   -- Reset
  formatError err

-- | Get error code for an error
getErrorCode :: CLIError -> ErrorCode
getErrorCode (CommandNotFound _) = ErrCommandNotFound
getErrorCode (InvalidArgument _ _) = ErrInvalidArgument
getErrorCode (SessionError _) = ErrSession
getErrorCode (NetworkError _) = ErrNetwork
getErrorCode (ConfigError _) = ErrConfig
getErrorCode (FileError _ _) = ErrFile
getErrorCode (UnknownError _) = ErrUnknown

-- ============================================================================
-- ERROR CREATION HELPERS
-- ============================================================================

-- | Create a command not found error
commandNotFound :: String -> CLIError
commandNotFound = CommandNotFound

-- | Create an invalid argument error
invalidArgument :: String -> String -> CLIError
invalidArgument = InvalidArgument

-- | Create a session error
sessionError :: String -> CLIError
sessionError = SessionError

-- | Create a network error
networkError :: String -> CLIError
networkError = NetworkError

-- | Create a config error
configError :: String -> CLIError
configError = ConfigError

-- | Create a file error
fileError :: String -> String -> CLIError
fileError = FileError

-- | Create an unknown error
unknownError :: String -> CLIError
unknownError = UnknownError
