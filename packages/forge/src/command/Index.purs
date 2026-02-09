{-|
Module      : Forge.Command.Index
Description : Slash Command System

Handles slash commands that can be invoked from the chat interface.
Commands are prefix-matched and can have custom implementations.

== Built-in Commands

| Command     | Description                          |
|-------------|--------------------------------------|
| /help       | Show help information                |
| /clear      | Clear the current session            |
| /compact    | Compact conversation history         |
| /config     | Show/edit configuration              |
| /bug        | Report a bug                         |
| /status     | Show system status                   |

== Custom Commands

Custom commands can be defined in `.forge/commands/`:
@
  .forge/commands/
    my-command.md
    another-command.md
@
-}
module Forge.Command.Index
  ( -- * Types
    Command
  , CommandResult
  , CommandContext
    -- * Command Operations
  , get
  , list
  , execute
  , parse
    -- * Built-in Commands
  , helpCommand
  , clearCommand
  , compactCommand
  , configCommand
  , statusCommand
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Command definition
type Command =
  { name :: String
  , description :: String
  , pattern :: String           -- Regex pattern for matching
  , usage :: String             -- Usage example
  , arguments :: Array String   -- Expected arguments
  }

-- | Command execution result
type CommandResult =
  { output :: String
  , success :: Boolean
  , data :: Maybe String  -- JSON data if applicable
  }

-- | Command execution context
type CommandContext =
  { sessionId :: Maybe String
  , workspaceRoot :: String
  , args :: Array String
  }

-- ============================================================================
-- FFI
-- ============================================================================

-- | Load custom commands from directory
foreign import loadCustomCommandsFFI :: String -> Aff (Array Command)

-- | Execute built-in command
foreign import executeBuiltinFFI :: String -> CommandContext -> Aff (Either String CommandResult)

-- ============================================================================
-- BUILT-IN COMMANDS
-- ============================================================================

helpCommand :: Command
helpCommand =
  { name: "help"
  , description: "Show help information about commands"
  , pattern: "^/help\\s*(.*)?$"
  , usage: "/help [command]"
  , arguments: ["command"]
  }

clearCommand :: Command
clearCommand =
  { name: "clear"
  , description: "Clear the current session or start a new one"
  , pattern: "^/clear$"
  , usage: "/clear"
  , arguments: []
  }

compactCommand :: Command
compactCommand =
  { name: "compact"
  , description: "Compact conversation history to save context"
  , pattern: "^/compact$"
  , usage: "/compact"
  , arguments: []
  }

configCommand :: Command
configCommand =
  { name: "config"
  , description: "Show or edit configuration"
  , pattern: "^/config\\s*(.*)?$"
  , usage: "/config [key] [value]"
  , arguments: ["key", "value"]
  }

statusCommand :: Command
statusCommand =
  { name: "status"
  , description: "Show system status and diagnostics"
  , pattern: "^/status$"
  , usage: "/status"
  , arguments: []
  }

builtInCommands :: Array Command
builtInCommands = 
  [ helpCommand
  , clearCommand
  , compactCommand
  , configCommand
  , statusCommand
  ]

-- ============================================================================
-- COMMAND OPERATIONS
-- ============================================================================

{-| Get a command by name. -}
get :: String -> Aff (Maybe Command)
get name = do
  -- Check built-in commands
  case Array.find (\c -> c.name == name) builtInCommands of
    Just cmd -> pure $ Just cmd
    Nothing -> do
      -- Check custom commands
      customCmds <- loadCustomCommandsFFI ".forge/commands"
      pure $ Array.find (\c -> c.name == name) customCmds

{-| List all available commands. -}
list :: Aff (Either String (Array Command))
list = do
  customCmds <- loadCustomCommandsFFI ".forge/commands"
  pure $ Right $ builtInCommands <> customCmds

{-| Execute a command by name. -}
execute :: String -> CommandContext -> Aff (Either String CommandResult)
execute name ctx = do
  cmd <- get name
  case cmd of
    Nothing -> pure $ Left ("Unknown command: /" <> name)
    Just _ -> executeBuiltinFFI name ctx

{-| Parse a command string into name and arguments.

Example: "/help clear" -> { name: "help", args: ["clear"] }
-}
parse :: String -> Maybe { name :: String, args :: Array String }
parse input
  | not (startsWith "/" input) = Nothing
  | otherwise =
      let trimmed = String.drop 1 input  -- Remove leading /
          parts = String.split (String.Pattern " ") trimmed
      in case Array.uncons parts of
        Nothing -> Nothing
        Just { head: name, tail: args } ->
          let cleanArgs = Array.filter (not <<< String.null) args
          in Just { name, args: cleanArgs }
  where
    startsWith prefix str = String.take (String.length prefix) str == prefix
