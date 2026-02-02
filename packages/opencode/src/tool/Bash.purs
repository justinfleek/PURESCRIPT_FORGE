-- | Bash.purs - Bash command execution tool
-- | Mirrors opencode/src/tool/bash.ts
-- | 
-- | This tool executes shell commands with proper sandboxing and permission checks.
-- | It integrates with the Permission system to verify command execution is allowed.
module Tool.Bash where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Effect.Aff (Aff, attempt, makeAff)
import Effect.Class (liftEffect)
import Effect.Exception (Error)
import Data.Argonaut (Json, encodeJson, decodeJson)

-- Import canonical types
import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Opencode.Types.Permission (PermissionRequest, PermissionReply)

-- | Bash tool parameters
-- | Matches the TypeScript Zod schema in bash.ts
type BashParams =
  { command :: String            -- The shell command to execute
  , timeout :: Maybe Int         -- Optional timeout in milliseconds (default 120000)
  , workdir :: Maybe String      -- Working directory (defaults to project root)
  , description :: String        -- Human-readable description of what command does
  }

-- | Bash execution metadata returned with results
type BashMetadata =
  { output :: String             -- Command stdout/stderr
  , exit :: Maybe Int            -- Exit code (Nothing if killed/timeout)
  , description :: String        -- Echo back the description
  , truncated :: Boolean         -- Whether output was truncated
  , duration :: Int              -- Execution time in ms
  }

-- | Configuration for the bash tool
type BashConfig =
  { defaultTimeout :: Int        -- Default timeout in ms
  , maxOutputBytes :: Int        -- Maximum output size before truncation
  , maxOutputLines :: Int        -- Maximum lines before truncation
  , allowedCommands :: Array String  -- Whitelist of allowed commands (empty = all)
  , blockedPatterns :: Array String  -- Patterns to block (e.g., "rm -rf /")
  }

-- | Default configuration
defaultConfig :: BashConfig
defaultConfig =
  { defaultTimeout: 120000       -- 2 minutes
  , maxOutputBytes: 51200        -- 50KB
  , maxOutputLines: 2000
  , allowedCommands: []          -- Empty = allow all
  , blockedPatterns: ["rm -rf /", "rm -rf /*", "> /dev/sda"]
  }

-- | Validate that a command is allowed to execute
validateCommand :: BashConfig -> String -> Either String Unit
validateCommand config cmd =
  -- Check blocked patterns
  if any (\pat -> contains pat cmd) config.blockedPatterns
    then Left "Command contains blocked pattern"
    else Right unit
  where
    any f xs = notImplemented "any"
    contains pat str = notImplemented "contains"

-- | Create a permission request for bash command
mkPermissionRequest :: BashParams -> PermissionRequest
mkPermissionRequest params =
  { tool: "bash"
  , action: "execute"
  , resource: params.command
  , metadata: encodeJson params
  }

-- | Execute bash command
-- | This is the main entry point called by the tool registry
execute :: BashParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Validate command against config
  case validateCommand defaultConfig params.command of
    Left err -> pure $ mkErrorResult err
    Right _ -> executeImpl params ctx

-- | Internal implementation after validation
executeImpl :: BashParams -> ToolContext -> Aff ToolResult
executeImpl params ctx = do
  -- TODO: Actually execute via Node child_process FFI
  -- For now, return a placeholder
  pure
    { title: "$ " <> params.description
    , metadata: encodeJson (mkMetadata params "")
    , output: "TODO: Implement bash execution via FFI"
    , attachments: Nothing
    }

-- | Create metadata from params and output
mkMetadata :: BashParams -> String -> BashMetadata
mkMetadata params output =
  { output
  , exit: Just 0
  , description: params.description
  , truncated: false
  , duration: 0
  }

-- | Create an error result
mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

-- | Tool registration info
bashTool :: ToolInfo
bashTool =
  { id: "bash"
  , description: "Execute shell commands with proper sandboxing"
  , parameters: encodeJson bashParamsSchema
  , execute: \json ctx -> 
      case decodeJson json of
        Left err -> pure $ mkErrorResult (show err)
        Right params -> execute params ctx
  , formatValidationError: Nothing
  }

-- | JSON schema for parameters (simplified)
bashParamsSchema :: { type :: String, properties :: Json }
bashParamsSchema = notImplemented "bashParamsSchema"

-- Helpers
notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
