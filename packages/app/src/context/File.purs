-- | File context - manages file loading and tree navigation
-- | Migrated from: forge-dev/packages/app/src/context/file.tsx
module App.Context.File
  ( FileSelection
  , SelectedLineRange
  , FileViewState
  , FileState
  , DirectoryState
  , FileStore
  , TreeStore
  , mkFileStore
  , mkTreeStore
  , selectionFromLines
  , normalizeSelectedLines
  , stripFileProtocol
  , stripQueryAndHash
  , unquoteGitPath
  , normalizePath
  , fileTab
  , pathFromTab
  ) where

import Prelude

import Data.Array (filter, length, (:))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), drop, indexOf, take, trim)
import Data.String as String
import Data.Int (fromString)

-- | File selection (character-level)
type FileSelection =
  { startLine :: Int
  , startChar :: Int
  , endLine :: Int
  , endChar :: Int
  }

-- | Selected line range
type SelectedLineRange =
  { start :: Int
  , end :: Int
  , side :: Maybe String  -- "additions" | "deletions"
  , endSide :: Maybe String
  }

-- | File view state (per-file UI state)
type FileViewState =
  { scrollTop :: Maybe Number
  , scrollLeft :: Maybe Number
  , selectedLines :: Maybe SelectedLineRange
  }

-- | File loading state
type FileState =
  { path :: String
  , name :: String
  , loaded :: Boolean
  , loading :: Boolean
  , error :: Maybe String
  , content :: Maybe String
  }

-- | Directory tree state
type DirectoryState =
  { expanded :: Boolean
  , loaded :: Boolean
  , loading :: Boolean
  , error :: Maybe String
  , children :: Array String
  }

-- | File store state
type FileStore =
  { files :: Map String FileState
  }

-- | Tree store state
type TreeStore =
  { nodes :: Map String { path :: String, nodeType :: String }  -- nodeType: "file" | "directory"
  , dirs :: Map String DirectoryState
  }

-- | Create initial file store
mkFileStore :: FileStore
mkFileStore = { files: Map.empty }

-- | Create initial tree store
mkTreeStore :: TreeStore
mkTreeStore =
  { nodes: Map.empty
  , dirs: Map.singleton "" { expanded: true, loaded: false, loading: false, error: Nothing, children: [] }
  }

-- | Strip file:// protocol from path
stripFileProtocol :: String -> String
stripFileProtocol input =
  let prefix = "file://"
  in
    if String.take (String.length prefix) input == prefix
    then String.drop (String.length prefix) input
    else input

-- | Strip query and hash from path
stripQueryAndHash :: String -> String
stripQueryAndHash input =
  let
    hashIndex = indexOf (Pattern "#") input
    queryIndex = indexOf (Pattern "?") input
  in
    case hashIndex, queryIndex of
      Just h, Just q -> String.take (min h q) input
      Just h, Nothing -> String.take h input
      Nothing, Just q -> String.take q input
      Nothing, Nothing -> input

-- | Unquote git-style quoted paths with octal escapes
unquoteGitPath :: String -> String
unquoteGitPath input =
  -- Simplified implementation - full version would handle octal escapes
  if String.take 1 input == "\"" && takeLast 1 input == "\""
  then String.drop 1 (dropLast 1 input)
  else input
  where
    takeLast n s = String.drop (String.length s - n) s
    dropLast n s = String.take (String.length s - n) s

-- | Convert selected line range to file selection
selectionFromLines :: SelectedLineRange -> FileSelection
selectionFromLines range =
  let
    startLine = min range.start range.end
    endLine = max range.start range.end
  in
    { startLine, endLine, startChar: 0, endChar: 0 }

-- | Normalize selected lines (ensure start <= end, swap sides if needed)
normalizeSelectedLines :: SelectedLineRange -> SelectedLineRange
normalizeSelectedLines range =
  if range.start <= range.end
  then range
  else
    { start: range.end
    , end: range.start
    , side: range.endSide
    , endSide: if range.side /= range.endSide then range.side else Nothing
    }

-- | Normalize a file path relative to root directory
normalizePath :: String -> String -> String
normalizePath root input =
  let
    path = input
      # stripFileProtocol
      # stripQueryAndHash
      # unquoteGitPath
    
    prefix = if String.takeRight 1 root == "/" then root else root <> "/"
    
    stripped =
      if String.take (String.length prefix) path == prefix
      then String.drop (String.length prefix) path
      else if String.take (String.length root) path == root
      then String.drop (String.length root) path
      else path
    
    -- Strip leading ./ or /
    final =
      if String.take 2 stripped == "./"
      then String.drop 2 stripped
      else if String.take 1 stripped == "/"
      then String.drop 1 stripped
      else stripped
  in
    final

-- | Create file tab value from path
fileTab :: String -> String
fileTab path = "file://" <> path

-- | Extract path from file tab value
pathFromTab :: String -> Maybe String
pathFromTab tabValue =
  let prefix = "file://"
  in
    if String.take (String.length prefix) tabValue == prefix
    then Just (String.drop (String.length prefix) tabValue)
    else Nothing

-- Helper for String.takeRight
takeRight :: Int -> String -> String
takeRight n s = String.drop (String.length s - n) s
