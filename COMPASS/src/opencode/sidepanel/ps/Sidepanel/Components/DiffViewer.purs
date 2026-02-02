-- | Diff Viewer Component - AI Change Visualization and Review Interface
-- |
-- | **What:** Displays file diffs (changes) from AI suggestions with accept/reject
-- |         functionality. Supports unified, split, and list view modes. Allows editing
-- |         changes before accepting and previewing files.
-- | **Why:** Enables users to review AI-generated code changes before applying them,
-- |         providing control over what changes are accepted and allowing modifications.
-- | **How:** Renders diffs organized by file, with hunks showing old/new lines. Supports
-- |         accepting/rejecting individual hunks or entire files. Provides edit dialog for
-- |         modifying changes and preview modal for viewing file contents. Loads diffs from
-- |         Bridge Server via WebSocket.
-- |
-- | Coeffect Equation:
-- |   DiffViewer : Input -> Component q Input Output m
-- |   with resource flow: WSClient^1 -o (Diff^n * Action^m) -o Output^k
-- |
-- | Module Structure:
-- |   DiffViewer.Types   - Type definitions (DiffHunk, FileDiff, State, Action, Output)
-- |   DiffViewer.Render  - All rendering functions
-- |   DiffViewer.Handler - Action handling logic
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.DiffViewer as DiffViewer
-- |
-- | -- In parent component:
-- | HH.slot _diff unit DiffViewer.component
-- |   { wsClient: wsClient }
-- |   (case _ of
-- |     DiffViewer.HunkAccepted file hunkId -> HandleHunkAccepted file hunkId
-- |     DiffViewer.AllAccepted -> HandleAllAccepted)
-- |
-- | -- Update diffs:
-- | H.query _diff unit $ H.tell $ DiffViewer.UpdateDiffs diffs
-- | ```
-- |
-- | Spec 59: AI Change Visualization - shows file diffs with accept/reject
module Sidepanel.Components.DiffViewer
  ( -- * Component
    component
    -- * Re-exports from Types
  , module Sidepanel.Components.DiffViewer.Types
  ) where

import Prelude
import Halogen as H
import Effect.Aff.Class (class MonadAff)
import Data.Maybe (Maybe(..))

-- Re-export types
import Sidepanel.Components.DiffViewer.Types
  ( DiffHunk
  , DiffStatus(..)
  , FileDiff
  , ViewMode(..)
  , State
  , Action(..)
  , Output(..)
  , Input
  , initialState
  , statusClass
  , statusText
  , countPending
  , findHunk
  , detectLanguage
  )

-- Internal imports
import Sidepanel.Components.DiffViewer.Render (render)
import Sidepanel.Components.DiffViewer.Handler (handleAction)

--------------------------------------------------------------------------------
-- | Component
--------------------------------------------------------------------------------

-- | Diff Viewer component
-- |
-- | Displays AI-generated code changes with accept/reject functionality.
-- | Supports multiple view modes: Unified, Split, and List.
component :: forall q m. MonadAff m => H.Component q Input Output m
component =
  H.mkComponent
    { initialState: \input -> initialState { wsClient = input.wsClient }
    , render
    , eval: H.mkEval $ H.defaultEval
        { handleAction = handleAction
        , initialize = Just Initialize
        , receive = Just <<< Receive
        }
    }
