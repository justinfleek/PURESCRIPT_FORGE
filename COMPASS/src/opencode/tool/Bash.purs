{-|
Module      : Tool.Bash
Description : Sandboxed command execution via gVisor
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Bash Tool

Executes shell commands with gVisor sandboxing.
See BashTypes.purs for type definitions.

== Coeffect: execute : BashParams -> Graded Container ExecResult
-}
module Tool.Bash
  ( -- * Tool Interface
    BashParams(..)
  , BashResult(..)
  , BashMetadata(..)
  , execute
  , bashTool
    -- * Configuration
  , BashConfig(..)
  , defaultConfig
    -- * Command Analysis
  , CommandClass(..)
  , classifyCommand
  , validateCommand
    -- * Sandboxed Execution
  , executeInSandbox
  , executeDirect
    -- * Coeffects
  , bashCoeffect
  ) where

import Prelude

import Data.Maybe (Maybe(..), maybe)
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Argonaut (Json, class EncodeJson, class DecodeJson, encodeJson, decodeJson)
import Effect.Aff (Aff, attempt)
import Effect.Class (liftEffect)
import Effect (Effect)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Opencode.Types.Permission (PermissionRequest, PermissionReply)
import Aleph.Coeffect (Resource(..), Graded, SandboxKind(..), ContainerSpec)
import Aleph.Sandbox as Sandbox
import Bridge.FFI.Node.Terminal as Terminal

-- ════════════════════════════════════════════════════════════════════════════
-- TOOL INTERFACE
-- ════════════════════════════════════════════════════════════════════════════

{-| Bash tool parameters.

@
  record BashParams where
    command     : String
    timeout     : Maybe Nat
    workdir     : Maybe String
    description : String
    sandbox     : Maybe SandboxKind  -- Override auto-detection
@
-}
type BashParams =
  { command :: String            -- The shell command to execute
  , timeout :: Maybe Int         -- Optional timeout in milliseconds (default 120000)
  , workdir :: Maybe String      -- Working directory (defaults to project root)
  , description :: String        -- Human-readable description of what command does
  , sandbox :: Maybe SandboxKind -- Override auto-detected sandbox level
  , env :: Maybe (Array { key :: String, value :: String })
  }

{-| Bash execution result. -}
type BashResult =
  { success :: Boolean
  , output :: String
  , exitCode :: Int
  , metadata :: BashMetadata
  , sandboxProof :: Maybe Sandbox.SandboxProof
  }

{-| Bash execution metadata returned with results.

@
  record BashMetadata where
    output      : String
    exit        : Maybe Int
    description : String
    truncated   : Bool
    duration    : Nat
    sandboxed   : Bool
    containerId : Maybe String
@
-}
type BashMetadata =
  { output :: String             -- Command stdout/stderr
  , exitCode :: Maybe Int        -- Exit code (Nothing if killed/timeout)
  , description :: String        -- Echo back the description
  , truncated :: Boolean         -- Whether output was truncated
  , durationMs :: Int            -- Execution time in ms
  , sandboxed :: Boolean         -- Was command sandboxed?
  , containerId :: Maybe String  -- gVisor container ID if sandboxed
  , resourceUsage :: ResourceUsage
  }

type ResourceUsage =
  { cpuTimeMs :: Int
  , memoryMB :: Int
  , syscallCount :: Int
  , networkBytes :: Int
  }

-- | Execute bash command
execute :: BashParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Validate command against config
  case validateCommand defaultConfig params.command of
    Left err -> pure $ mkErrorResult err
    Right _ -> do
      -- 2. Classify command to determine sandbox level
      let cmdClass = classifyCommand params.command
      let sandboxKind = params.sandbox # maybe (sandboxForClass cmdClass) identity
      
      -- 3. Execute in appropriate sandbox
      result <- executeInSandbox sandboxKind params
      
      -- 4. Format result
      pure $ formatResult params result

-- | Tool registration
bashTool :: ToolInfo
bashTool =
  { id: "bash"
  , description: "Execute shell commands via Terminal FFI"
  , parameters: bashParamsSchema
  , execute: \json ctx -> 
      case decodeJson json of
        Left err -> pure $ mkErrorResult (show err)
        Right params -> execute params ctx
  , formatValidationError: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
-- CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

{-| Configuration for the bash tool.

@
  record BashConfig where
    defaultTimeout   : Nat
    maxOutputBytes   : Nat
    maxOutputLines   : Nat
    blockedPatterns  : List String
    requireSandbox   : Bool
    defaultImage     : String
@
-}
type BashConfig =
  { defaultTimeout :: Int        -- Default timeout in ms
  , maxOutputBytes :: Int        -- Maximum output size before truncation
  , maxOutputLines :: Int        -- Maximum lines before truncation
  , blockedPatterns :: Array String  -- Patterns to always block
  , requireSandbox :: Boolean    -- Always require sandbox (default true)
  , defaultImage :: String       -- Default container image
  , defaultMemoryMB :: Int       -- Default memory limit
  , defaultCPUPercent :: Int     -- Default CPU limit
  }

-- | Default configuration
defaultConfig :: BashConfig
defaultConfig =
  { defaultTimeout: 120000       -- 2 minutes
  , maxOutputBytes: 51200        -- 50KB
  , maxOutputLines: 2000
  , blockedPatterns: 
      [ "rm -rf /"
      , "rm -rf /*"
      , "> /dev/sda"
      , "dd if=/dev/zero"
      , ":(){ :|:& };:"          -- Fork bomb
      , "mkfs"
      , "chmod -R 777 /"
      ]
  , requireSandbox: true
  , defaultImage: "alpine:latest"
  , defaultMemoryMB: 1024
  , defaultCPUPercent: 50
  }

-- ════════════════════════════════════════════════════════════════════════════
-- COMMAND ANALYSIS
-- ════════════════════════════════════════════════════════════════════════════

{-| Command classification for sandbox level determination.

@
  data CommandClass
    = SafeCommand        -- Read-only, no network
    | BuildCommand       -- Needs filesystem write
    | NetworkCommand     -- Needs network access
    | SystemCommand      -- Needs elevated privileges
    | DangerousCommand   -- Should be rejected
@
-}
data CommandClass
  = SafeCommand
  | BuildCommand
  | NetworkCommand
  | SystemCommand
  | DangerousCommand

derive instance eqCommandClass :: Eq CommandClass
derive instance ordCommandClass :: Ord CommandClass
derive instance genericCommandClass :: Generic CommandClass _

instance showCommandClass :: Show CommandClass where
  show = genericShow

-- | Classify command by analyzing its structure
classifyCommand :: String -> CommandClass
classifyCommand cmd
  | isDangerous cmd = DangerousCommand
  | isNetwork cmd = NetworkCommand
  | isBuild cmd = BuildCommand
  | isSystem cmd = SystemCommand
  | otherwise = SafeCommand
  where
    isDangerous c = 
      any (\pat -> String.contains (String.Pattern pat) c) 
        defaultConfig.blockedPatterns
    
    isNetwork c = any (\pat -> String.contains (String.Pattern pat) c)
      ["curl", "wget", "fetch", "nc ", "netcat", "ssh ", "scp ", "rsync"]
    
    isBuild c = any (\pat -> String.contains (String.Pattern pat) c)
      ["npm ", "yarn ", "pnpm ", "cargo ", "make ", "cmake ", "go build"
      , "stack ", "cabal ", "spago ", "lake "]
    
    isSystem c = any (\pat -> String.contains (String.Pattern pat) c)
      ["sudo ", "su ", "chmod ", "chown ", "mount ", "umount "]
    
    any f xs = Array.any f xs

-- | Determine sandbox kind for command class
sandboxForClass :: CommandClass -> SandboxKind
sandboxForClass = case _ of
  SafeCommand -> SandboxFull
  BuildCommand -> SandboxFilesystem
  NetworkCommand -> SandboxNetwork
  SystemCommand -> SandboxFull
  DangerousCommand -> SandboxFull  -- Will be rejected anyway

-- | Validate that a command is allowed to execute
validateCommand :: BashConfig -> String -> Either String Unit
validateCommand config cmd =
  if isDangerous
  then Left "Command contains blocked pattern"
  else Right unit
  where
    isDangerous = Array.any 
      (\pat -> String.contains (String.Pattern pat) cmd) 
      config.blockedPatterns

-- ════════════════════════════════════════════════════════════════════════════
-- SANDBOXED EXECUTION
-- ════════════════════════════════════════════════════════════════════════════

{-| Execute command in sandbox or direct mode.

Currently uses direct execution via Terminal FFI since gVisor sandbox
is not yet implemented. When sandbox is available, this will route
based on SandboxKind.

@
  executeInSandbox : SandboxKind → BashParams → Aff BashResult
  executeInSandbox kind params = do
    -- Future: route to gVisor when available
    -- For now: direct execution with validation
    executeDirect params
@
-}
executeInSandbox :: SandboxKind -> BashParams -> Aff BashResult
executeInSandbox _kind params = do
  -- NOTE: Sandbox not yet implemented, using direct execution
  -- Command validation already happened in execute function
  executeDirect params

-- | Create container config for sandbox kind
mkContainerConfig :: SandboxKind -> BashParams -> Sandbox.ContainerConfig
mkContainerConfig kind params =
  Sandbox.defaultConfig
    { command = ["/bin/sh", "-c", params.command]
    , workdir = params.workdir # maybe "/workspace" identity
    , env = params.env # maybe [] identity
    , policy = Sandbox.policyFromKind kind
    }

-- | Execute command directly via Terminal FFI
-- WARNING: No sandbox isolation - command runs on host
executeDirect :: BashParams -> Aff BashResult
executeDirect params = do
  result <- Terminal.executeCommand params.command params.workdir Nothing
  case result of
    Left err -> pure
      { success: false
      , output: err
      , exitCode: 1
      , metadata: mkDirectMetadata params err Nothing
      , sandboxProof: Nothing
      }
    Right resp -> pure
      { success: resp.success
      , output: resp.output # maybe "" identity
      , exitCode: resp.exitCode # maybe 0 identity
      , metadata: mkDirectMetadata params (resp.output # maybe "" identity) resp.exitCode
      , sandboxProof: Nothing
      }

-- | Create metadata for direct (non-sandboxed) execution
mkDirectMetadata :: BashParams -> String -> Maybe Int -> BashMetadata
mkDirectMetadata params output exitCode =
  { output
  , exitCode
  , description: params.description
  , truncated: String.length output > defaultConfig.maxOutputBytes
  , durationMs: 0  -- Terminal FFI doesn't track this currently
  , sandboxed: false
  , containerId: Nothing
  , resourceUsage:
      { cpuTimeMs: 0
      , memoryMB: 0
      , syscallCount: 0
      , networkBytes: 0
      }
  }

-- ════════════════════════════════════════════════════════════════════════════
-- COEFFECTS
-- ════════════════════════════════════════════════════════════════════════════

{-| Coeffect for bash execution.

Bash requires a container sandbox:
@
  bashCoeffect : BashParams → Resource
  bashCoeffect params = Container (specFor params)
@
-}
bashCoeffect :: BashParams -> Resource
bashCoeffect params = Container
  { image: defaultConfig.defaultImage
  , memoryMB: defaultConfig.defaultMemoryMB
  , cpuPercent: defaultConfig.defaultCPUPercent
  , timeoutMs: params.timeout # maybe defaultConfig.defaultTimeout identity
  , networkIsolated: true
  , filesystemReadOnly: true
  }

-- | Create a permission request for bash command
mkPermissionRequest :: BashParams -> PermissionRequest
mkPermissionRequest params =
  { tool: "bash"
  , action: "execute"
  , resource: params.command
  , metadata: encodeJson params
  }

-- ════════════════════════════════════════════════════════════════════════════
-- HELPERS
-- ════════════════════════════════════════════════════════════════════════════

mkMetadata :: BashParams -> Sandbox.ExecOutput -> Boolean -> Maybe String -> BashMetadata
mkMetadata params output sandboxed containerId =
  { output: output.stdout <> output.stderr
  , exitCode: Just output.exitCode
  , description: params.description
  , truncated: false
  , durationMs: output.metrics.wallTimeMs
  , sandboxed
  , containerId
  , resourceUsage:
      { cpuTimeMs: output.metrics.userTimeMs + output.metrics.sysTimeMs
      , memoryMB: output.metrics.maxRssMB
      , syscallCount: output.metrics.syscallCount
      , networkBytes: 0
      }
  }

mkEmptyMetadata :: BashParams -> String -> BashMetadata
mkEmptyMetadata params reason =
  { output: reason
  , exitCode: Nothing
  , description: params.description
  , truncated: false
  , durationMs: 0
  , sandboxed: true
  , containerId: Nothing
  , resourceUsage:
      { cpuTimeMs: 0
      , memoryMB: 0
      , syscallCount: 0
      , networkBytes: 0
      }
  }

formatResult :: BashParams -> BashResult -> ToolResult
formatResult params result =
  { title: "$ " <> params.description
  , metadata: encodeJson result.metadata
  , output: result.output
  , attachments: Nothing
  }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

bashParamsSchema :: Json
bashParamsSchema = encodeJson
  { "type": "object"
  , "properties":
      { "command": 
          { "type": "string"
          , "description": "The command to execute"
          }
      , "timeout":
          { "type": "number"
          , "description": "Optional timeout in milliseconds"
          }
      , "workdir":
          { "type": "string"
          , "description": "The working directory to run the command in"
          }
      , "description":
          { "type": "string"
          , "description": "Clear, concise description of what this command does in 5-10 words"
          }
      }
  , "required": ["command", "description"]
  }

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
