-- | FileContextView Types
-- |
-- | Type definitions for the file context view component.
-- |
-- | Coeffect Equation:
-- |   Types : FileInContext^n -> DirectoryGroup^m -> ContextBudget
-- |   with grouping: Files -o Directories
-- |
-- | Module Coverage: FileInContext, FileStatus, DirectoryGroup, State, Action, Output
module Sidepanel.Components.FileContextView.Types
  ( -- * File Types
    FileInContext
  , FileStatus(..)
  , DirectoryGroup
  , ContextBudget
    -- * Component Types
  , State
  , Action(..)
  , Output(..)
  , Input
    -- * Initial State
  , initialState
    -- * Helpers
  , groupFilesByDirectory
  , calculateBudget
  , detectLanguage
  ) where

import Prelude
import Data.Array (filter, foldl, snoc)
import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..))
import Data.String as String
import Sidepanel.WebSocket.Client as WS

--------------------------------------------------------------------------------
-- | File Types
--------------------------------------------------------------------------------

-- | File in context
type FileInContext =
  { path :: String
  , tokens :: Int
  , readAt :: Number
  , status :: FileStatus
  , language :: String
  , size :: Int
  }

-- | File status
data FileStatus
  = Active       -- Currently in context
  | Stale        -- In context but not recently referenced
  | Recommended  -- Should be added to context

derive instance eqFileStatus :: Eq FileStatus

-- | Directory grouping
type DirectoryGroup =
  { path :: String
  , files :: Array FileInContext
  , totalTokens :: Int
  }

-- | Context budget
type ContextBudget =
  { used :: Int
  , total :: Int
  , percentage :: Number
  }

--------------------------------------------------------------------------------
-- | Component Types
--------------------------------------------------------------------------------

-- | Component state
type State =
  { files :: Array FileInContext
  , groupedFiles :: Array DirectoryGroup
  , selectedFiles :: Array String
  , contextBudget :: ContextBudget
  , filterQuery :: String
  , showStale :: Boolean
  , showRecommended :: Boolean
  , wsClient :: Maybe WS.WSClient
  , previewFile :: Maybe String
  , previewContent :: Maybe String
  }

-- | Component actions
data Action
  = Initialize
  | UpdateFiles (Array FileInContext)
  | ToggleFileSelection String
  | SelectAll
  | DeselectAll
  | RemoveSelected
  | AddRecommended String
  | UpdateFilter String
  | ToggleShowStale
  | ToggleShowRecommended
  | RefreshContext
  | ClearAll
  | OpenPreview String
  | ClosePreview
  | HandleCodeCopied String
  | HandleCodeAddedToChat String
  | NoOp

-- | Component output
data Output
  = FilesRemoved (Array String)
  | FilesAdded (Array String)
  | ContextRefreshed

-- | Component input
type Input = { wsClient :: Maybe WS.WSClient }

--------------------------------------------------------------------------------
-- | Initial State
--------------------------------------------------------------------------------

-- | Initial component state
initialState :: State
initialState =
  { files: []
  , groupedFiles: []
  , selectedFiles: []
  , contextBudget:
      { used: 0
      , total: 80000
      , percentage: 0.0
      }
  , filterQuery: ""
  , showStale: true
  , showRecommended: true
  , wsClient: Nothing
  , previewFile: Nothing
  , previewContent: Nothing
  }

--------------------------------------------------------------------------------
-- | Helpers
--------------------------------------------------------------------------------

-- | Group files by directory
groupFilesByDirectory :: Array FileInContext -> Array DirectoryGroup
groupFilesByDirectory files =
  let
    groups = foldl (\acc file ->
      let dir = getDirectoryPath file.path
          existingIndex = Array.findIndex (\g -> g.path == dir) acc
      in case existingIndex of
        Just index -> case Array.updateAt index (\g -> g { files = snoc g.files file, totalTokens = g.totalTokens + file.tokens }) acc of
          Just updated -> updated
          Nothing -> acc
        Nothing -> snoc acc { path: dir, files: [file], totalTokens: file.tokens }
    ) [] files
  in
    groups
  where
    getDirectoryPath :: String -> String
    getDirectoryPath path = case String.lastIndexOf (Pattern "/") path of
      Just index -> String.take index path
      Nothing -> "/"

-- | Calculate context budget
calculateBudget :: Array FileInContext -> Int -> ContextBudget
calculateBudget files total =
  let used = foldl (\acc f -> acc + f.tokens) 0 files
      percentage = if total > 0 then (Int.toNumber used / Int.toNumber total) * 100.0 else 0.0
  in
    { used
    , total
    , percentage
    }

-- | Detect language from file path
detectLanguage :: String -> Maybe String
detectLanguage path =
  let
    ext = case String.lastIndexOf (Pattern ".") path of
      Just idx -> String.drop (idx + 1) path
      Nothing -> ""
  in
    case ext of
      "ts" -> Just "typescript"
      "tsx" -> Just "tsx"
      "js" -> Just "javascript"
      "jsx" -> Just "jsx"
      "hs" -> Just "haskell"
      "purs" -> Just "purescript"
      "lean" -> Just "lean"
      "py" -> Just "python"
      "rs" -> Just "rust"
      "go" -> Just "go"
      "java" -> Just "java"
      "cpp" -> Just "cpp"
      "c" -> Just "c"
      "h" -> Just "c"
      "hpp" -> Just "cpp"
      "md" -> Just "markdown"
      "json" -> Just "json"
      "yaml" -> Just "yaml"
      "yml" -> Just "yaml"
      "toml" -> Just "toml"
      "css" -> Just "css"
      "html" -> Just "html"
      "xml" -> Just "xml"
      "sql" -> Just "sql"
      "sh" -> Just "bash"
      "bash" -> Just "bash"
      "ps1" -> Just "powershell"
      _ -> Just "text"
