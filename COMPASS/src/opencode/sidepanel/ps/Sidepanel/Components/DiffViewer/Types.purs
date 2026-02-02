-- | DiffViewer Types
-- |
-- | Type definitions for the diff viewer component.
-- |
-- | Coeffect Equation:
-- |   DiffTypes : Hunk^n -> FileDiff^m -> ViewMode -> State
-- |   with status tracking: Pending | Accepted | Rejected | Modified
-- |
-- | Module Coverage: Core types, state, actions, outputs
module Sidepanel.Components.DiffViewer.Types
  ( -- * Diff Types
    DiffHunk
  , DiffStatus(..)
  , FileDiff
  , ViewMode(..)
    -- * Component Types
  , State
  , Action(..)
  , Output(..)
  , Input
    -- * Initial State
  , initialState
    -- * Utilities
  , statusClass
  , statusText
  , countPending
  , findHunk
  , detectLanguage
  ) where

import Prelude
import Data.Array (filter, foldl, length)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..))
import Data.String as String
import Sidepanel.WebSocket.Client as WS

--------------------------------------------------------------------------------
-- | Diff Types
--------------------------------------------------------------------------------

-- | Diff hunk (change block)
type DiffHunk =
  { id :: String
  , file :: String
  , lineStart :: Int
  , lineEnd :: Int
  , oldLines :: Array String
  , newLines :: Array String
  , explanation :: String
  , status :: DiffStatus
  }

-- | Diff status
data DiffStatus
  = Pending   -- Not yet accepted/rejected
  | Accepted
  | Rejected
  | Modified  -- User edited the change

derive instance eqDiffStatus :: Eq DiffStatus

-- | File diff (collection of hunks)
type FileDiff =
  { file :: String
  , hunks :: Array DiffHunk
  , timestamp :: Number
  , message :: String
  , isNewFile :: Boolean
  }

-- | View mode
data ViewMode
  = Unified  -- Unified diff view
  | Split    -- Side-by-side view
  | List     -- List of changes

derive instance eqViewMode :: Eq ViewMode

--------------------------------------------------------------------------------
-- | Component Types
--------------------------------------------------------------------------------

-- | Component state
type State =
  { diffs :: Array FileDiff
  , selectedFile :: Maybe String
  , selectedHunk :: Maybe String
  , viewMode :: ViewMode
  , pendingCount :: Int
  , editingHunk :: Maybe String    -- hunkId being edited
  , editContent :: String          -- current edit content
  , previewFile :: Maybe String    -- file being previewed
  , previewContent :: Maybe String -- preview file content
  , wsClient :: Maybe WS.WSClient
  }

-- | Component actions
data Action
  = Initialize
  | Receive Input
  | UpdateDiffs (Array FileDiff)
  | SelectFile String
  | SelectHunk String
  | AcceptHunk String
  | RejectHunk String
  | AcceptAllInFile String
  | RejectAllInFile String
  | AcceptAll
  | RejectAll
  | OpenEditDialog String      -- hunkId
  | UpdateEditContent String
  | SaveEdit String            -- hunkId
  | CancelEdit
  | EditHunk String String     -- hunkId, newContent
  | ChangeViewMode ViewMode
  | OpenPreview String         -- file path
  | ClosePreview
  | PreviewFile String
  | HandleCodeCopied String
  | HandleCodeAddedToChat String
  | NoOp

-- | Component output
data Output
  = HunkAccepted String String -- file, hunkId
  | HunkRejected String String
  | AllAcceptedInFile String
  | AllRejectedInFile String
  | AllAccepted
  | AllRejected
  | FilePreviewed String

-- | Component input
type Input = { wsClient :: Maybe WS.WSClient }

--------------------------------------------------------------------------------
-- | Initial State
--------------------------------------------------------------------------------

-- | Initial component state
initialState :: State
initialState =
  { diffs: []
  , selectedFile: Nothing
  , selectedHunk: Nothing
  , viewMode: Unified
  , pendingCount: 0
  , editingHunk: Nothing
  , editContent: ""
  , previewFile: Nothing
  , previewContent: Nothing
  , wsClient: Nothing
  }

--------------------------------------------------------------------------------
-- | Utilities
--------------------------------------------------------------------------------

-- | Get CSS class for status
statusClass :: DiffStatus -> String
statusClass = case _ of
  Pending -> "pending"
  Accepted -> "accepted"
  Rejected -> "rejected"
  Modified -> "modified"

-- | Get display text for status
statusText :: DiffStatus -> String
statusText = case _ of
  Pending -> "Pending"
  Accepted -> "Accepted"
  Rejected -> "Rejected"
  Modified -> "Modified"

-- | Count pending hunks across all diffs
countPending :: Array FileDiff -> Int
countPending diffs =
  foldl (\acc diff -> acc + length (filter (\h -> h.status == Pending) diff.hunks)) 0 diffs

-- | Find a hunk by ID across all diffs
findHunk :: String -> Array FileDiff -> Maybe { file :: String, hunk :: DiffHunk }
findHunk hunkId diffs =
  Array.findMap searchInDiff diffs
  where
    searchInDiff :: FileDiff -> Maybe { file :: String, hunk :: DiffHunk }
    searchInDiff diff =
      Array.findMap (\hunk -> if hunk.id == hunkId then Just { file: diff.file, hunk } else Nothing) diff.hunks

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
