-- | CLI Error handling
module Opencode.CLI.Error where

import Prelude
import Effect (Effect)
import Effect.Console as Console
import Opencode.CLI.UI as UI

-- | Error types for CLI operations
data CLIError
  = CommandNotFound String
  | InvalidArgument String
  | SessionError String
  | NetworkError String
  | UnknownError String

-- | Display a CLI error to the user
displayError :: CLIError -> Effect Unit
displayError err = do
  let formatted = formatError err
  UI.error formatted

-- | Format error for output
formatError :: CLIError -> String
formatError (CommandNotFound cmd) = "Command not found: " <> cmd
formatError (InvalidArgument arg) = "Invalid argument: " <> arg
formatError (SessionError msg) = "Session error: " <> msg
formatError (NetworkError msg) = "Network error: " <> msg
formatError (UnknownError msg) = "Error: " <> msg
