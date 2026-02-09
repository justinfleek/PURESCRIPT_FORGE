{-|
Module      : Forge.Tool.Ls
Description : Directory listing tool
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
module Forge.Tool.Ls
  ( -- * Tool Interface
    LsParams
  , execute
  , lsTool
    -- * Configuration
  , ignorePatterns
  , fileLimit
    -- * Types
  , DirTree
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Set (Set)
import Data.Set as Set
import Data.Map (Map)
import Data.Map as Map
import Data.Argonaut (Json, encodeJson, decodeJson, (.:?), printJsonDecodeError)
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Tool result type
type ToolResult =
  { title :: String
  , output :: String
  , metadata :: Json
  , attachments :: Maybe (Array Json)
  }

-- | Tool context
type ToolContext = 
  { workspaceRoot :: String
  }

-- | Tool info
type ToolInfo =
  { id :: String
  , description :: String
  , parameters :: Json
  , execute :: Json -> ToolContext -> Aff ToolResult
  , formatValidationError :: Maybe (Json -> String)
  }

-- | Directory entry from FFI
type DirEntry =
  { name :: String
  , isDirectory :: Boolean
  }

-- ============================================================================
-- FFI
-- ============================================================================

-- | FFI for directory listing
foreign import listDirectoryFFI :: String -> Aff (Either String (Array DirEntry))

-- ============================================================================
-- CONFIGURATION
-- ============================================================================

-- | Default patterns to ignore
ignorePatterns :: Array String
ignorePatterns =
  [ "node_modules"
  , "__pycache__"
  , ".git"
  , "dist"
  , "build"
  , "target"
  , "vendor"
  , "bin"
  , "obj"
  , ".idea"
  , ".vscode"
  , ".zig-cache"
  , "zig-out"
  , ".coverage"
  , "coverage"
  , "tmp"
  , "temp"
  , ".cache"
  , "cache"
  , "logs"
  , ".venv"
  , "venv"
  , "env"
  , ".spago"
  , "output"
  , ".psci_modules"
  ]

-- | Maximum files to return
fileLimit :: Int
fileLimit = 100

-- ============================================================================
-- PARAMS AND TYPES
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
  let searchPath = fromMaybe ctx.workspaceRoot params.path
  
  -- 2. Build ignore set
  let ignores = ignorePatterns <> fromMaybe [] params.ignore
  
  -- 3. List directory contents recursively
  result <- listDirectoryRecursive searchPath ignores 0
  case result of
    Left err -> pure $ mkErrorResult ("Failed to list directory: " <> err)
    Right entries -> do
      let files = Array.filter (not <<< _.isDirectory) entries
      let dirs = Array.filter _.isDirectory entries
      let truncated = Array.length files > fileLimit
      let limitedFiles = Array.take fileLimit files
      
      -- 4. Build tree structure
      let tree = buildTree searchPath limitedFiles
      
      -- 5. Render output
      let output = renderTree searchPath tree
      
      pure
        { title: searchPath
        , metadata: encodeJson
            { count: Array.length limitedFiles
            , totalFiles: Array.length files
            , totalDirs: Array.length dirs
            , truncated
            }
        , output
        , attachments: Nothing
        }

-- | Recursively list directory contents
listDirectoryRecursive :: String -> Array String -> Int -> Aff (Either String (Array { name :: String, isDirectory :: Boolean, path :: String }))
listDirectoryRecursive dir ignores depth
  | depth > 10 = pure $ Right [] -- Max depth limit
  | otherwise = do
      listResult <- listDirectoryFFI dir
      case listResult of
        Left err -> pure $ Left err
        Right entries -> do
          -- Filter ignored entries
          let filtered = Array.filter (\e -> not (shouldIgnore e.name ignores)) entries
          
          -- Add full path
          let withPath = map (\e -> { name: e.name, isDirectory: e.isDirectory, path: dir <> "/" <> e.name }) filtered
          
          -- Recursively list subdirectories
          subResults <- Array.foldM (\acc entry -> 
            if entry.isDirectory
              then do
                subList <- listDirectoryRecursive entry.path ignores (depth + 1)
                case subList of
                  Left _ -> pure acc -- Skip errors in subdirs
                  Right subEntries -> pure $ acc <> subEntries
              else pure acc
          ) withPath (Array.filter _.isDirectory withPath)
          
          pure $ Right subResults

-- | Check if name should be ignored
shouldIgnore :: String -> Array String -> Boolean
shouldIgnore name patterns =
  Array.any (\p -> name == p || String.contains (String.Pattern p) name) patterns

{-| Tool registration. -}
lsTool :: ToolInfo
lsTool =
  { id: "list"
  , description: lsDescription
  , parameters: lsSchema
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
buildTree :: String -> Array { name :: String, isDirectory :: Boolean, path :: String } -> DirTree
buildTree rootPath entries =
  let paths = map _.path entries
      dirs = Array.foldMap extractDirs paths # Set.fromFoldable
      filesByDir = Array.foldl groupByDir Map.empty paths
  in { dirs, filesByDir }
  where
    extractDirs :: String -> Array String
    extractDirs filePath =
      let parts = String.split (String.Pattern "/") filePath
          dirParts = Array.take (Array.length parts - 1) parts
      in Array.mapWithIndex (\idx _ -> String.joinWith "/" (Array.take (idx + 1) dirParts)) dirParts
    
    groupByDir :: Map String (Array String) -> String -> Map String (Array String)
    groupByDir acc filePath =
      let parts = String.split (String.Pattern "/") filePath
          dir = if Array.length parts > 1
                then String.joinWith "/" (Array.take (Array.length parts - 1) parts)
                else rootPath
          fileName = Array.last parts # fromMaybe filePath
      in Map.insertWith (<>) dir [fileName] acc

{-| Render directory tree as string. -}
renderTree :: String -> DirTree -> String
renderTree rootPath tree =
  let dirList = Set.toUnfoldable tree.dirs :: Array String
      sortedDirs = Array.sort dirList
      rootFiles = Map.lookup rootPath tree.filesByDir # fromMaybe []
  in rootPath <> "/\n" <>
     String.joinWith "" (map (\f -> "  " <> f <> "\n") rootFiles) <>
     renderSubdirs sortedDirs tree.filesByDir rootPath 1
  where
    renderSubdirs :: Array String -> Map String (Array String) -> String -> Int -> String
    renderSubdirs dirs fileMap parentDir indent =
      let childDirs = Array.filter (isDirectChild parentDir) dirs
          indentStr = String.joinWith "" (Array.replicate indent "  ")
      in String.joinWith "" $ map (\dir ->
           let dirName = Array.last (String.split (String.Pattern "/") dir) # fromMaybe dir
               files = Map.lookup dir fileMap # fromMaybe []
               subTree = renderSubdirs dirs fileMap dir (indent + 1)
           in indentStr <> dirName <> "/\n" <>
              String.joinWith "" (map (\f -> indentStr <> "  " <> f <> "\n") files) <>
              subTree
         ) childDirs
    
    isDirectChild :: String -> String -> Boolean
    isDirectChild parent child =
      let prefix = parent <> "/"
          prefixLen = String.length prefix
      in String.take prefixLen child == prefix &&
         not (String.contains (String.Pattern "/") (String.drop prefixLen child))

-- ============================================================================
-- HELPERS
-- ============================================================================

lsDescription :: String
lsDescription =
  "Lists files and directories in a tree structure. " <>
  "Use this to understand project structure before making changes."

lsSchema :: Json
lsSchema = encodeJson
  { "type": "object"
  , "properties":
      { "path": 
          { "type": "string"
          , "description": "Directory path to list (defaults to current directory)" 
          }
      , "ignore": 
          { "type": "array"
          , "items": { "type": "string" }
          , "description": "Additional ignore patterns" 
          }
      }
  }

decodeLsParams :: Json -> Either String LsParams
decodeLsParams json =
  case decodeLsParamsImpl json of
    Left err -> Left (printJsonDecodeError err)
    Right result -> Right result
  where
    decodeLsParamsImpl j = do
      obj <- decodeJson j
      path <- obj .:? "path"
      ignore <- obj .:? "ignore"
      pure { path, ignore }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "List Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationError :: Json -> String
formatValidationError _ = "Invalid ls parameters"
