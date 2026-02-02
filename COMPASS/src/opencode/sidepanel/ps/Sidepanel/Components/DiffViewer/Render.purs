-- | DiffViewer Render Functions
-- |
-- | Rendering functions for the diff viewer component.
-- |
-- | Coeffect Equation:
-- |   Render : State -> H.ComponentHTML Action () m
-- |   with view modes: Unified | Split | List
-- |
-- | Module Coverage: Header, diff list, hunks, modals
module Sidepanel.Components.DiffViewer.Render
  ( render
  , renderHeader
  , renderDiffList
  , renderFileDiff
  , renderHunk
  , renderUnifiedHunk
  , renderSplitHunk
  , renderListHunk
  , renderEditDialog
  , renderPreviewModal
  ) where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Data.Array (mapWithIndex, length, map)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (joinWith)
import Sidepanel.Components.CodeSelection as CodeSelection
import Sidepanel.Components.DiffViewer.Types
  ( State
  , Action(..)
  , DiffHunk
  , DiffStatus(..)
  , FileDiff
  , ViewMode(..)
  , statusClass
  , statusText
  , findHunk
  , detectLanguage
  )

--------------------------------------------------------------------------------
-- | Main Render
--------------------------------------------------------------------------------

-- | Main render function
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "diff-viewer") ]
    [ renderHeader state
    , renderDiffList state.diffs state.selectedFile state.viewMode
    , renderEditDialog state
    , renderPreviewModal state
    ]

--------------------------------------------------------------------------------
-- | Header
--------------------------------------------------------------------------------

-- | Render header with controls
renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.div
    [ HP.class_ (H.ClassName "diff-header") ]
    [ HH.h3_ [ HH.text $ "Changes (" <> show state.pendingCount <> " pending)" ]
    , HH.div
        [ HP.class_ (H.ClassName "header-controls") ]
        [ HH.button
            [ HP.class_ (H.ClassName "btn-accept-all")
            , HE.onClick \_ -> AcceptAll
            ]
            [ HH.text "Accept All" ]
        , HH.button
            [ HP.class_ (H.ClassName "btn-reject-all")
            , HE.onClick \_ -> RejectAll
            ]
            [ HH.text "Reject All" ]
        , HH.div
            [ HP.class_ (H.ClassName "view-mode-toggle") ]
            [ HH.button
                [ HP.class_ (H.ClassName $ if state.viewMode == Unified then "active" else "")
                , HE.onClick \_ -> ChangeViewMode Unified
                ]
                [ HH.text "Unified" ]
            , HH.button
                [ HP.class_ (H.ClassName $ if state.viewMode == Split then "active" else "")
                , HE.onClick \_ -> ChangeViewMode Split
                ]
                [ HH.text "Split" ]
            , HH.button
                [ HP.class_ (H.ClassName $ if state.viewMode == List then "active" else "")
                , HE.onClick \_ -> ChangeViewMode List
                ]
                [ HH.text "List" ]
            ]
        ]
    ]

--------------------------------------------------------------------------------
-- | Diff List
--------------------------------------------------------------------------------

-- | Render list of file diffs
renderDiffList :: forall m. Array FileDiff -> Maybe String -> ViewMode -> H.ComponentHTML Action () m
renderDiffList diffs selectedFile viewMode =
  HH.div
    [ HP.class_ (H.ClassName "diff-list") ]
    (mapWithIndex (\index diff -> renderFileDiff index diff selectedFile viewMode) diffs)

-- | Render a single file diff
renderFileDiff :: forall m. Int -> FileDiff -> Maybe String -> ViewMode -> H.ComponentHTML Action () m
renderFileDiff index diff selectedFile viewMode =
  HH.div
    [ HP.class_ (H.ClassName $ "file-diff " <> if selectedFile == Just diff.file then "selected" else "")
    , HE.onClick \_ -> SelectFile diff.file
    ]
    [ HH.div
        [ HP.class_ (H.ClassName "file-diff-header") ]
        [ HH.span
            [ HP.class_ (H.ClassName "file-name") ]
            [ HH.text diff.file ]
        , HH.span
            [ HP.class_ (H.ClassName "file-meta") ]
            [ HH.text $ show (length diff.hunks) <> " changes" ]
        , HH.span
            [ HP.class_ (H.ClassName "file-message") ]
            [ HH.text diff.message ]
        , HH.button
            [ HP.class_ (H.ClassName "btn-accept-file")
            , HE.onClick \e -> do
                H.stopPropagation e
                AcceptAllInFile diff.file
            ]
            [ HH.text "Accept All" ]
        , HH.button
            [ HP.class_ (H.ClassName "btn-reject-file")
            , HE.onClick \e -> do
                H.stopPropagation e
                RejectAllInFile diff.file
            ]
            [ HH.text "Reject All" ]
        , HH.button
            [ HP.class_ (H.ClassName "btn-preview-file")
            , HE.onClick \e -> do
                H.stopPropagation e
                PreviewFile diff.file
            ]
            [ HH.text "Preview" ]
        ]
    , if selectedFile == Just diff.file then
        HH.div
          [ HP.class_ (H.ClassName "file-diff-content") ]
          (map (\hunk -> renderHunk hunk viewMode) diff.hunks)
      else
        HH.text ""
    ]

--------------------------------------------------------------------------------
-- | Hunk Rendering
--------------------------------------------------------------------------------

-- | Render a hunk based on view mode
renderHunk :: forall m. DiffHunk -> ViewMode -> H.ComponentHTML Action () m
renderHunk hunk viewMode =
  case viewMode of
    Unified -> renderUnifiedHunk hunk
    Split -> renderSplitHunk hunk
    List -> renderListHunk hunk

-- | Render unified diff view
renderUnifiedHunk :: forall m. DiffHunk -> H.ComponentHTML Action () m
renderUnifiedHunk hunk =
  HH.div
    [ HP.class_ (H.ClassName $ "diff-hunk " <> statusClass hunk.status) ]
    [ HH.div
        [ HP.class_ (H.ClassName "hunk-header") ]
        [ HH.text $ "Change at lines " <> show hunk.lineStart <> "-" <> show hunk.lineEnd ]
    , HH.div
        [ HP.class_ (H.ClassName "hunk-content") ]
        [ -- Old lines with code selection
          HH.slot (H.Slot "old" unit) unit CodeSelection.component
            { codeLines: hunk.oldLines
            , filePath: Just hunk.file
            , language: detectLanguage hunk.file
            }
            (case _ of
              CodeSelection.Copied code -> HandleCodeCopied code
              CodeSelection.AddedToChat code -> HandleCodeAddedToChat code
              CodeSelection.SelectionChanged _ -> NoOp)
        , -- New lines with code selection
          HH.slot (H.Slot "new" unit) unit CodeSelection.component
            { codeLines: hunk.newLines
            , filePath: Just hunk.file
            , language: detectLanguage hunk.file
            }
            (case _ of
              CodeSelection.Copied code -> HandleCodeCopied code
              CodeSelection.AddedToChat code -> HandleCodeAddedToChat code
              CodeSelection.SelectionChanged _ -> NoOp)
        ]
    , HH.div
        [ HP.class_ (H.ClassName "hunk-explanation") ]
        [ HH.text hunk.explanation ]
    , HH.div
        [ HP.class_ (H.ClassName "hunk-actions") ]
        [ HH.button
            [ HP.class_ (H.ClassName "btn-accept")
            , HE.onClick \_ -> AcceptHunk hunk.id
            ]
            [ HH.text "Accept" ]
        , HH.button
            [ HP.class_ (H.ClassName "btn-reject")
            , HE.onClick \_ -> RejectHunk hunk.id
            ]
            [ HH.text "Reject" ]
        , HH.button
            [ HP.class_ (H.ClassName "btn-edit")
            , HE.onClick \_ -> OpenEditDialog hunk.id
            ]
            [ HH.text "Edit" ]
        ]
    ]

-- | Render split diff view
renderSplitHunk :: forall m. DiffHunk -> H.ComponentHTML Action () m
renderSplitHunk hunk =
  HH.div
    [ HP.class_ (H.ClassName "diff-hunk-split") ]
    [ HH.div
        [ HP.class_ (H.ClassName "split-original") ]
        [ HH.h4_ [ HH.text "Original" ]
        , HH.div
            [ HP.class_ (H.ClassName "hunk-old") ]
            (mapWithIndex (\_ line -> HH.div [ HP.class_ (H.ClassName "line") ] [ HH.text line ]) hunk.oldLines)
        ]
    , HH.div
        [ HP.class_ (H.ClassName "split-modified") ]
        [ HH.h4_ [ HH.text "Modified" ]
        , HH.div
            [ HP.class_ (H.ClassName "hunk-new") ]
            (mapWithIndex (\_ line -> HH.div [ HP.class_ (H.ClassName "line") ] [ HH.text line ]) hunk.newLines)
        ]
    , HH.div
        [ HP.class_ (H.ClassName "hunk-explanation") ]
        [ HH.text hunk.explanation ]
    , HH.div
        [ HP.class_ (H.ClassName "hunk-actions") ]
        [ HH.button
            [ HP.class_ (H.ClassName "btn-accept")
            , HE.onClick \_ -> AcceptHunk hunk.id
            ]
            [ HH.text "Accept" ]
        , HH.button
            [ HP.class_ (H.ClassName "btn-reject")
            , HE.onClick \_ -> RejectHunk hunk.id
            ]
            [ HH.text "Reject" ]
        ]
    ]

-- | Render list view
renderListHunk :: forall m. DiffHunk -> H.ComponentHTML Action () m
renderListHunk hunk =
  HH.div
    [ HP.class_ (H.ClassName "diff-hunk-list") ]
    [ HH.span
        [ HP.class_ (H.ClassName "hunk-summary") ]
        [ HH.text $ hunk.file <> ":" <> show hunk.lineStart <> "-" <> show hunk.lineEnd ]
    , HH.span
        [ HP.class_ (H.ClassName "hunk-status") ]
        [ HH.text $ statusText hunk.status ]
    , HH.button
        [ HP.class_ (H.ClassName "btn-accept")
        , HE.onClick \_ -> AcceptHunk hunk.id
        ]
        [ HH.text "Accept" ]
    , HH.button
        [ HP.class_ (H.ClassName "btn-reject")
        , HE.onClick \_ -> RejectHunk hunk.id
        ]
        [ HH.text "Reject" ]
    ]

--------------------------------------------------------------------------------
-- | Modals
--------------------------------------------------------------------------------

-- | Render edit dialog
renderEditDialog :: forall m. State -> H.ComponentHTML Action () m
renderEditDialog state =
  case state.editingHunk of
    Just hunkId ->
      case findHunk hunkId state.diffs of
        Just { hunk } ->
          HH.div
            [ HP.class_ (H.ClassName "modal-overlay")
            , HE.onClick \_ -> CancelEdit
            ]
            [ HH.div
                [ HP.class_ (H.ClassName "modal")
                , HE.onClick \e -> H.stopPropagation e
                ]
                [ HH.div
                    [ HP.class_ (H.ClassName "modal-header") ]
                    [ HH.h3_ [ HH.text $ "Edit Change: " <> hunk.file <> ":" <> show hunk.lineStart <> "-" <> show hunk.lineEnd ]
                    , HH.button
                        [ HP.class_ (H.ClassName "btn-close")
                        , HE.onClick \_ -> CancelEdit
                        ]
                        [ HH.text "x" ]
                    ]
                , HH.div
                    [ HP.class_ (H.ClassName "modal-body") ]
                    [ HH.div
                        [ HP.class_ (H.ClassName "edit-original") ]
                        [ HH.h4_ [ HH.text "Original:" ]
                        , HH.pre
                            [ HP.class_ (H.ClassName "code-block") ]
                            [ HH.text (joinWith "\n" hunk.oldLines) ]
                        ]
                    , HH.div
                        [ HP.class_ (H.ClassName "edit-new") ]
                        [ HH.h4_ [ HH.text "Modified:" ]
                        , HH.textarea
                            [ HP.class_ (H.ClassName "edit-textarea")
                            , HP.value state.editContent
                            , HE.onValueInput UpdateEditContent
                            , HP.rows 10
                            ]
                        ]
                    ]
                , HH.div
                    [ HP.class_ (H.ClassName "modal-footer") ]
                    [ HH.button
                        [ HP.class_ (H.ClassName "btn btn-secondary")
                        , HE.onClick \_ -> CancelEdit
                        ]
                        [ HH.text "Cancel" ]
                    , HH.button
                        [ HP.class_ (H.ClassName "btn btn-primary")
                        , HE.onClick \_ -> SaveEdit hunkId
                        ]
                        [ HH.text "Save Changes" ]
                    ]
                ]
            ]
        Nothing ->
          HH.text ""
    Nothing ->
      HH.text ""

-- | Render preview modal
renderPreviewModal :: forall m. State -> H.ComponentHTML Action () m
renderPreviewModal state =
  case state.previewFile of
    Just file ->
      HH.div
        [ HP.class_ (H.ClassName "modal-overlay")
        , HE.onClick \_ -> ClosePreview
        ]
        [ HH.div
            [ HP.class_ (H.ClassName "modal modal-large")
            , HE.onClick \e -> H.stopPropagation e
            ]
            [ HH.div
                [ HP.class_ (H.ClassName "modal-header") ]
                [ HH.h3_ [ HH.text $ "Preview: " <> file ]
                , HH.button
                    [ HP.class_ (H.ClassName "btn-close")
                    , HE.onClick \_ -> ClosePreview
                    ]
                    [ HH.text "x" ]
                ]
            , HH.div
                [ HP.class_ (H.ClassName "modal-body") ]
                [ HH.pre
                    [ HP.class_ (H.ClassName "file-preview") ]
                    [ HH.text (fromMaybe "" state.previewContent) ]
                ]
            , HH.div
                [ HP.class_ (H.ClassName "modal-footer") ]
                [ HH.button
                    [ HP.class_ (H.ClassName "btn btn-primary")
                    , HE.onClick \_ -> ClosePreview
                    ]
                    [ HH.text "Close" ]
                ]
            ]
        ]
    Nothing ->
      HH.text ""
