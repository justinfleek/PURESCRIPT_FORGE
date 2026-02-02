{-|
Module      : Tool.BashTypes
Description : Type definitions for Bash tool
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Bash Types

Extracted type definitions for the Bash tool.
Contains params, results, config, and classification types.

== System F-ω Encoding

@
  BashParams  : Record of command execution parameters
  BashResult  : Record of execution results with proof
  BashConfig  : Record of tool configuration
  CommandClass: ADT for command safety classification
@

-}
module Tool.BashTypes
  ( -- * Parameter Types
    BashParams(..)
  , BashResult(..)
  , BashMetadata(..)
  , ResourceUsage(..)
    -- * Configuration
  , BashConfig(..)
  , defaultConfig
    -- * Command Classification
  , CommandClass(..)
  , SandboxKind(..)
  , sandboxForClass
    -- * Sandbox Types
  , Resource(..)
  , ContainerSpec
  , PermissionRequest
    -- * Tool Types
  , ToolResult
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Argonaut (Json)

-- ════════════════════════════════════════════════════════════════════════════
-- PARAMETER TYPES
-- ════════════════════════════════════════════════════════════════════════════

-- | Parameters for bash command execution
type BashParams =
  { command :: String           -- Command to execute
  , timeout :: Maybe Int        -- Timeout in milliseconds
  , workdir :: Maybe String     -- Working directory
  , env :: Maybe (Array { key :: String, value :: String })  -- Environment variables
  , description :: String       -- Human-readable description
  }

-- | Result of bash command execution
type BashResult =
  { success :: Boolean
  , output :: String
  , exitCode :: Int
  , metadata :: BashMetadata
  , sandboxProof :: Maybe String  -- Proof of sandbox execution
  }

-- | Metadata about the execution
type BashMetadata =
  { output :: String
  , exitCode :: Maybe Int
  , description :: String
  , truncated :: Boolean
  , durationMs :: Int
  , sandboxed :: Boolean
  , containerId :: Maybe String
  , resourceUsage :: ResourceUsage
  }

-- | Resource usage metrics
type ResourceUsage =
  { cpuTimeMs :: Int
  , memoryMB :: Int
  , syscallCount :: Int
  , networkBytes :: Int
  }

-- ════════════════════════════════════════════════════════════════════════════
-- CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

-- | Configuration for the bash tool
type BashConfig =
  { defaultTimeout :: Int
  , maxOutputBytes :: Int
  , maxOutputLines :: Int
  , blockedPatterns :: Array String
  , requireSandbox :: Boolean
  , defaultImage :: String
  , defaultMemoryMB :: Int
  , defaultCPUPercent :: Int
  }

-- | Default configuration
defaultConfig :: BashConfig
defaultConfig =
  { defaultTimeout: 120000
  , maxOutputBytes: 51200
  , maxOutputLines: 2000
  , blockedPatterns: 
      [ "rm -rf /"
      , "rm -rf /*"
      , "> /dev/sda"
      , "dd if=/dev/zero"
      , ":(){ :|:& };:"
      , "mkfs"
      , "chmod -R 777 /"
      ]
  , requireSandbox: true
  , defaultImage: "alpine:latest"
  , defaultMemoryMB: 1024
  , defaultCPUPercent: 50
  }

-- ════════════════════════════════════════════════════════════════════════════
-- COMMAND CLASSIFICATION
-- ════════════════════════════════════════════════════════════════════════════

-- | Command classification for sandbox level determination
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

-- | Sandbox isolation level
data SandboxKind
  = SandboxFull        -- Full isolation (read-only FS, no network)
  | SandboxFilesystem  -- Filesystem access allowed, isolated network
  | SandboxNetwork     -- Network access allowed, read-only FS
  | SandboxMinimal     -- Minimal isolation (syscall filtering only)

derive instance eqSandboxKind :: Eq SandboxKind
derive instance genericSandboxKind :: Generic SandboxKind _

instance showSandboxKind :: Show SandboxKind where
  show = genericShow

-- | Determine sandbox kind for command class
sandboxForClass :: CommandClass -> SandboxKind
sandboxForClass = case _ of
  SafeCommand -> SandboxFull
  BuildCommand -> SandboxFilesystem
  NetworkCommand -> SandboxNetwork
  SystemCommand -> SandboxFull
  DangerousCommand -> SandboxFull

-- ════════════════════════════════════════════════════════════════════════════
-- SANDBOX TYPES
-- ════════════════════════════════════════════════════════════════════════════

-- | Container specification
type ContainerSpec =
  { image :: String
  , memoryMB :: Int
  , cpuPercent :: Int
  , timeoutMs :: Int
  , networkIsolated :: Boolean
  , filesystemReadOnly :: Boolean
  }

-- | Resource requirement (coeffect)
data Resource
  = Container ContainerSpec
  | Network
  | Filesystem String

-- | Permission request
type PermissionRequest =
  { tool :: String
  , action :: String
  , resource :: String
  , metadata :: Json
  }

-- ════════════════════════════════════════════════════════════════════════════
-- TOOL TYPES
-- ════════════════════════════════════════════════════════════════════════════

-- | Tool result format
type ToolResult =
  { title :: String
  , metadata :: Json
  , output :: String
  , attachments :: Maybe (Array { mime :: String, url :: String })
  }
