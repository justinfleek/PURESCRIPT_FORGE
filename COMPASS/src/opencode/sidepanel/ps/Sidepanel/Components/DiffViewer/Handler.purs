-- | DiffViewer Action Handler
-- |
-- | Action handling logic for the diff viewer component.
-- |
-- | Coeffect Equation:
-- |   Handler : Action -> H.HalogenM State Action () Output m Unit
-- |   with state transitions: State -o State'
-- |
-- | Module Coverage: Initialize, hunk operations, edit, preview
module Sidepanel.Components.DiffViewer.Handler
  ( handleAction
  ) where

import Prelude
import Halogen as H
import Effect.Aff.Class (class MonadAff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..))
import Data.String as String
import Sidepanel.Api.Bridge as Bridge
import Sidepanel.Components.DiffViewer.Types
  ( State
  , Action(..)
  , Output(..)
  , DiffStatus(..)
  , countPending
  , findHunk
  )

--------------------------------------------------------------------------------
-- | Action Handler
--------------------------------------------------------------------------------

-- | Handle component actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Load diffs from bridge server
    state <- H.get
    case state.wsClient of
      Just wsClient -> do
        -- Request diffs via WebSocket (would use session.diff API when available)
        -- For now, initialize with empty state - diffs will be loaded when session.diff API is implemented
        pure unit
      Nothing -> pure unit
  
  Receive input -> do
    H.modify_ \s -> s { wsClient = input.wsClient }
  
  UpdateDiffs diffs -> do
    let pendingCount = countPending diffs
    H.modify_ \s -> s { diffs = diffs, pendingCount = pendingCount }
  
  SelectFile file -> do
    H.modify_ \s -> s { selectedFile = Just file }
  
  SelectHunk hunkId -> do
    H.modify_ \s -> s { selectedHunk = Just hunkId }
  
  AcceptHunk hunkId -> do
    state <- H.get
    case findHunk hunkId state.diffs of
      Just { file, hunk } -> do
        H.raise (HunkAccepted file hunkId)
        -- Update hunk status
        let updatedDiffs = map (\diff -> diff { hunks = map (\h -> if h.id == hunkId then h { status = Accepted } else h) diff.hunks }) state.diffs
        H.modify_ \s -> s { diffs = updatedDiffs, pendingCount = countPending updatedDiffs }
      Nothing ->
        pure unit
  
  RejectHunk hunkId -> do
    state <- H.get
    case findHunk hunkId state.diffs of
      Just { file, hunk } -> do
        H.raise (HunkRejected file hunkId)
        -- Update hunk status
        let updatedDiffs = map (\diff -> diff { hunks = map (\h -> if h.id == hunkId then h { status = Rejected } else h) diff.hunks }) state.diffs
        H.modify_ \s -> s { diffs = updatedDiffs, pendingCount = countPending updatedDiffs }
      Nothing ->
        pure unit
  
  AcceptAllInFile file -> do
    H.raise (AllAcceptedInFile file)
    state <- H.get
    let updatedDiffs = map (\diff -> if diff.file == file then diff { hunks = map (\hunk -> hunk { status = Accepted }) diff.hunks } else diff) state.diffs
    H.modify_ \s -> s { diffs = updatedDiffs, pendingCount = countPending updatedDiffs }
  
  RejectAllInFile file -> do
    H.raise (AllRejectedInFile file)
    state <- H.get
    let updatedDiffs = map (\diff -> if diff.file == file then diff { hunks = map (\hunk -> hunk { status = Rejected }) diff.hunks } else diff) state.diffs
    H.modify_ \s -> s { diffs = updatedDiffs, pendingCount = countPending updatedDiffs }
  
  AcceptAll -> do
    H.raise AllAccepted
    H.modify_ \s -> s 
      { diffs = map (\diff -> diff { hunks = map (\hunk -> hunk { status = Accepted }) diff.hunks }) s.diffs
      , pendingCount = 0
      }
  
  RejectAll -> do
    H.raise AllRejected
    H.modify_ \s -> s
      { diffs = map (\diff -> diff { hunks = map (\hunk -> hunk { status = Rejected }) diff.hunks }) s.diffs
      , pendingCount = 0
      }
  
  OpenEditDialog hunkId -> do
    state <- H.get
    case findHunk hunkId state.diffs of
      Just { hunk } -> do
        -- Initialize edit content with new lines
        let content = String.joinWith "\n" hunk.newLines
        H.modify_ \s -> s { editingHunk = Just hunkId, editContent = content }
      Nothing ->
        pure unit
  
  UpdateEditContent content -> do
    H.modify_ \s -> s { editContent = content }
  
  SaveEdit hunkId -> do
    state <- H.get
    let newLines = String.split (Pattern "\n") state.editContent
    -- Update the hunk with edited content
    H.modify_ \s -> s
      { diffs = map (\diff -> diff { hunks = map (\hunk -> if hunk.id == hunkId then hunk { newLines = newLines, status = Modified } else hunk) diff.hunks }) s.diffs
      , editingHunk = Nothing
      , editContent = ""
      }
  
  CancelEdit -> do
    H.modify_ \s -> s { editingHunk = Nothing, editContent = "" }
  
  EditHunk hunkId newContent -> do
    -- Legacy action - now handled by SaveEdit
    handleAction (SaveEdit hunkId)
  
  ChangeViewMode mode -> do
    H.modify_ \s -> s { viewMode = mode }
  
  OpenPreview file -> do
    H.raise (FilePreviewed file)
    state <- H.get
    case state.wsClient of
      Just client -> do
        result <- H.liftAff $ Bridge.readFileContent client { path: file }
        case result of
          Right response -> do
            H.modify_ \s -> s { previewFile = Just file, previewContent = response.content }
          Left err -> do
            H.modify_ \s -> s { previewFile = Just file, previewContent = Just ("Error loading file: " <> err.message) }
      Nothing -> do
        H.modify_ \s -> s { previewFile = Just file, previewContent = Just "Not connected to bridge server" }
  
  ClosePreview -> do
    H.modify_ \s -> s { previewFile = Nothing, previewContent = Nothing }
  
  PreviewFile file -> do
    handleAction (OpenPreview file)
  
  HandleCodeCopied code -> do
    -- Code was copied to clipboard - could show notification
    pure unit
  
  HandleCodeAddedToChat code -> do
    -- Code was added to chat (copied with formatting) - could show notification
    pure unit
  
  NoOp ->
    pure unit
