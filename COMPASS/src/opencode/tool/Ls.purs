{-|
Module      : Tool.Ls
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
    -- * FFI
  , listDirectory
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
import Data.Argonaut (Json, class EncodeJson, encodeJson, decodeJson, (.:), (.:?))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo, ToolMetadata(..))
import Aleph.Coeffect (Resource(..))

-- | FFI for directory listing
foreign import listDirectory :: String -> Aff (Either String (Array { name :: String, isDirectory :: Boolean }))

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
  
  -- 3. List directory contents
  listResult <- listDirectory searchPath
  case listResult of
    Left err -> pure $ mkErrorResult ("Failed to list directory: " <> err)
    Right entries -> do
      -- Filter ignored patterns and build file list
      let allFiles = Array.mapMaybe (\e -> if e.isDirectory then Nothing else Just (searchPath <> "/" <> e.name)) entries
      let allDirs = Array.mapMaybe (\e -> if e.isDirectory then Just (searchPath <> "/" <> e.name) else Nothing) entries
      let filteredFiles = filterIgnored allFiles ignores
      let filteredDirs = filterIgnored allDirs ignores
      let files = Array.take fileLimit filteredFiles
      let truncated = Array.length filteredFiles >= fileLimit
      
      -- 4. Build tree structure
      let tree = buildTree files
      
      -- 5. Render output
      let output = renderTree searchPath tree
      
      pure
        { title: searchPath
        , metadata: LsMetadata
            { count: Array.length files
            , totalFiles: Array.length filteredFiles
            , totalDirs: Array.length filteredDirs
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

-- | Filter files/dirs by ignore patterns
filterIgnored :: Array String -> Array String -> Array String
filterIgnored paths ignores =
  Array.filter (\path -> not (shouldIgnore path ignores)) paths
  where
    shouldIgnore :: String -> Array String -> Boolean
    shouldIgnore path patterns =
      Array.any (\pattern -> String.contains (String.Pattern pattern) path) patterns

{-| Build directory tree from file list. -}
buildTree :: Array String -> DirTree
buildTree files =
  let dirs = Array.foldMap extractDirs files # Set.fromFoldable
      filesByDir = Array.foldl groupByDir Map.empty files
  in { dirs, filesByDir }
  where
    extractDirs :: String -> Array String
    extractDirs filePath =
      let parts = String.split (String.Pattern "/") filePath
          dirs = Array.take (Array.length parts - 1) parts
      in Array.mapWithIndex (\idx _ -> String.joinWith "/" (Array.take (idx + 1) parts)) dirs
    
    groupByDir :: Map String (Array String) -> String -> Map String (Array String)
    groupByDir acc filePath =
      let parts = String.split (String.Pattern "/") filePath
          dir = if Array.length parts > 1
                then String.joinWith "/" (Array.take (Array.length parts - 1) parts)
                else "."
          fileName = Array.last parts # fromMaybe filePath
      in Map.insertWith (<>) dir [fileName] acc

{-| Render directory tree as string. -}
renderTree :: String -> DirTree -> String
renderTree rootPath tree =
  let rootDir = if String.null rootPath then "." else rootPath
      dirList = Set.toUnfoldable tree.dirs # Array.sort
      fileMap = tree.filesByDir
      rootFiles = Map.lookup rootDir fileMap # fromMaybe []
      subdirs = Array.filter (\d -> d /= rootDir) dirList
  in rootDir <> "/\n" <>
     String.joinWith "" (Array.map (\f -> "  " <> f <> "\n") rootFiles) <>
     String.joinWith "" (Array.map (\d -> renderSubdir d fileMap 1) subdirs)
  where
    renderSubdir :: String -> Map String (Array String) -> Int -> String
    renderSubdir dir fileMap indent =
      let indentStr = String.joinWith "" (Array.replicate indent "  ")
          files = Map.lookup dir fileMap # fromMaybe []
          subdirs = Map.keys fileMap # Array.filter (\d -> String.startsWith (String.Pattern (dir <> "/")) d && d /= dir)
          dirName = Array.last (String.split (String.Pattern "/") dir) # fromMaybe dir
      in indentStr <> dirName <> "/\n" <>
         String.joinWith "" (Array.map (\f -> indentStr <> "  " <> f <> "\n") files) <>
         String.joinWith "" (Array.map (\d -> renderSubdir d fileMap (indent + 1)) subdirs)

-- ============================================================================
-- HELPERS
-- ============================================================================

lsDescription :: String
lsDescription =
  "Lists files and directories in a tree structure. " <>
  "Use this to understand project structure before making changes."

lsSchema :: Json
lsSchema = encodeJson
  { type: "object"
  , properties:
      { path: { type: "string", description: "Directory path to list (defaults to current directory)" }
      , ignore: { type: "array", items: { type: "string" }, description: "Additional ignore patterns" }
      }
  }

decodeLsParams :: Json -> Either String LsParams
decodeLsParams json = do
  obj <- decodeJson json
  path <- (obj .:? "path" >>= \mb -> pure (mb >>= decodeJson))
  ignore <- (obj .:? "ignore" >>= \mb -> pure (mb >>= decodeJson))
  pure { path, ignore }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "List Error"
  , metadata: ErrorMetadata { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationError :: Json -> String
formatValidationError _ = "Invalid ls parameters"

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
