-- | CLI Error handling
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/error.ts
module Forge.CLI.Error where

import Prelude
import Effect (Effect)
import Forge.Util.NotImplemented (notImplemented)

-- | Error types for CLI operations
data CLIError
  = CommandNotFound String
  | InvalidArgument String
  | SessionError String
  | NetworkError String
  | UnknownError String

-- | Display a CLI error to the user
displayError :: CLIError -> Effect Unit
displayError err = notImplemented "CLI.Error.displayError"

-- | Format error for output
formatError :: CLIError -> String
formatError (CommandNotFound cmd) = "Command not found: " <> cmd
formatError (InvalidArgument arg) = "Invalid argument: " <> arg
formatError (SessionError msg) = "Session error: " <> msg
formatError (NetworkError msg) = "Network error: " <> msg
formatError (UnknownError msg) = "Error: " <> msg
