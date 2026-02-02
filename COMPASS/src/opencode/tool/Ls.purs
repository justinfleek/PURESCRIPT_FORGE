{-|
Module      : Tool.Ls
Description : Directory listing tool
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Directory Listing Tool

Lists files and directories in a tree structure. Uses ripgrep for
efficient file discovery with automatic filtering of common
non-essential directories.

== Coeffect Equation

@
  ls : LsParams -> Graded (Filesystem path) ToolResult

  -- Requires:
  -- 1. Filesystem read access to target directory
@

== Default Ignore Patterns

The following directories are ignored by default:
- node_modules, __pycache__, .git, dist, build
- target, vendor, bin, obj, .idea, .vscode
- .zig-cache, coverage, tmp, temp, cache
- logs, .venv, venv, env

== Output Format

@
  /path/to/directory/
    subdir/
      file1.ts
      file2.ts
    file3.ts
@
-}
module Tool.Ls
  ( -- * Tool Interface
    LsParams(..)
  , execute
  , lsTool
    -- * Configuration
  , ignorePatterns
  , fileLimit
    -- * Types
  , DirTree(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Set (Set)
import Data.Set as Set
import Data.Map (Map)
import Data.Map as Map
import Data.Argonaut (Json, class EncodeJson, encodeJson, decodeJson)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Aleph.Coeffect (Resource(..))

-- ============================================================================
-- CONFIGURATION
-- ============================================================================

-- | Default patterns to ignore
ignorePatterns :: Array String
ignorePatterns =
  [ "node_modules/"
  , "__pycache__/"
  , ".git/"
  , "dist/"
  , "build/"
  , "target/"
  , "vendor/"
  , "bin/"
  , "obj/"
  , ".idea/"
  , ".vscode/"
  , ".zig-cache/"
  , "zig-out"
  , ".coverage"
  , "coverage/"
  , "tmp/"
  , "temp/"
  , ".cache/"
  , "cache/"
  , "logs/"
  , ".venv/"
  , "venv/"
  , "env/"
  ]

-- | Maximum files to return
fileLimit :: Int
fileLimit = 100

-- ============================================================================
-- TYPES
-- ============================================================================

{-| Parameters for ls tool.

@
  record LsParams where
    path   : Maybe String      -- Directory to list (defaults to cwd)
    ignore : Maybe (Array String)  -- Additional ignore patterns
@
-}
type LsParams =
  { path :: Maybe String
  , ignore :: Maybe (Array String)
  }

{-| Directory tree structure for output. -}
type DirTree =
  { dirs :: Set String
  , filesByDir :: Map String (Array String)
  }

-- ============================================================================
-- TOOL INTERFACE
-- ============================================================================

{-| Execute ls tool.

Lists files in the specified directory as a tree structure.
-}
execute :: LsParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Resolve path
  let searchPath = fromMaybe "." params.path
  
  -- 2. Build ignore globs
  let ignores = ignorePatterns <> fromMaybe [] params.ignore
  
  -- 3. Find files using ripgrep
  -- TODO: Call ripgrep to list files
  let files = [] :: Array String
  let truncated = Array.length files >= fileLimit
  
  -- 4. Build tree structure
  let tree = buildTree files
  
  -- 5. Render output
  let output = renderTree searchPath tree
  
  pure
    { title: searchPath
    , metadata: encodeJson
        { count: Array.length files
        , truncated
        }
    , output
    , attachments: Nothing
    }
  where
    fromMaybe :: forall a. a -> Maybe a -> a
    fromMaybe def Nothing = def
    fromMaybe _ (Just x) = x

{-| Tool registration. -}
lsTool :: ToolInfo
lsTool =
  { id: "list"
  , description: lsDescription
  , parameters: encodeJson lsSchema
  , execute: \json ctx ->
      case decodeLsParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Just formatValidationError
  }

-- ============================================================================
-- TREE BUILDING
-- ============================================================================

{-| Build directory tree from file list. -}
buildTree :: Array String -> DirTree
buildTree files =
  { dirs: Set.empty  -- TODO: Extract directories from paths
  , filesByDir: Map.empty  -- TODO: Group files by parent dir
  }

{-| Render directory tree as string. -}
renderTree :: String -> DirTree -> String
renderTree rootPath tree =
  rootPath <> "/\n"
  -- TODO: Recursively render subdirectories and files

-- ============================================================================
-- HELPERS
-- ============================================================================

lsDescription :: String
lsDescription =
  "Lists files and directories in a tree structure. " <>
  "Use this to understand project structure before making changes."

lsSchema :: { type :: String }
lsSchema = { type: "object" }

decodeLsParams :: Json -> Either String LsParams
decodeLsParams _ = notImplemented "decodeLsParams"

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "List Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationError :: Json -> String
formatValidationError _ = "Invalid ls parameters"

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
