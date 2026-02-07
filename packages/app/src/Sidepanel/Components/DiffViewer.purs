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
-- | **Dependencies:**
-- | - `Sidepanel.WebSocket.Client`: WebSocket communication
-- | - `Sidepanel.Api.Bridge`: Bridge API methods for file operations
-- |
-- | **Mathematical Foundation:**
-- | - **Pending Count:** Counts hunks with status `Pending` across all files.
-- | - **Hunk Status:** Hunks can be Pending, Accepted, Rejected, or Modified (user edited).
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
module Sidepanel.Components.DiffViewer where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Data.Array (filter, mapWithIndex, length, snoc, foldl, findMap)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), contains, split, joinWith)
import Data.Array as Array
import Sidepanel.WebSocket.Client as WS
import Sidepanel.Api.Bridge as Bridge
import Sidepanel.Components.CodeSelection as CodeSelection

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
  = Pending -- Not yet accepted/rejected
  | Accepted
  | Rejected
  | Modified -- User edited the change

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
  = Unified -- Unified diff view
  | Split -- Side-by-side view
  | List -- List of changes

derive instance eqViewMode :: Eq ViewMode

-- | Component state
type State =
  { diffs :: Array FileDiff
  , selectedFile :: Maybe String
  , selectedHunk :: Maybe String
  , viewMode :: ViewMode
  , pendingCount :: Int
  , editingHunk :: Maybe String -- hunkId being edited
  , editContent :: String -- current edit content
  , previewFile :: Maybe String -- file being previewed
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
  | OpenEditDialog String -- hunkId
  | UpdateEditContent String
  | SaveEdit String -- hunkId
  | CancelEdit
  | EditHunk String String -- hunkId, newContent
  | ChangeViewMode ViewMode
  | OpenPreview String -- file path
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

-- | Diff Viewer component
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

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "diff-viewer") ]
    [ renderHeader state
    , renderDiffList state.diffs state.selectedFile state.viewMode
    , renderEditDialog state
    , renderPreviewModal state
    ]

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

renderDiffList :: forall m. Array FileDiff -> Maybe String -> ViewMode -> H.ComponentHTML Action () m
renderDiffList diffs selectedFile viewMode =
  HH.div
    [ HP.class_ (H.ClassName "diff-list") ]
    (mapWithIndex (\index diff -> renderFileDiff index diff selectedFile viewMode) diffs)

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
            , HE.onClick \_ -> AcceptAllInFile diff.file
            ]
            [ HH.text "Accept All" ]
        , HH.button
            [ HP.class_ (H.ClassName "btn-reject-file")
            , HE.onClick \_ -> RejectAllInFile diff.file
            ]
            [ HH.text "Reject All" ]
        , HH.button
            [ HP.class_ (H.ClassName "btn-preview-file")
            , HE.onClick \_ -> PreviewFile diff.file
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

renderHunk :: forall m. DiffHunk -> ViewMode -> H.ComponentHTML Action () m
renderHunk hunk viewMode =
  case viewMode of
    Unified -> renderUnifiedHunk hunk
    Split -> renderSplitHunk hunk
    List -> renderListHunk hunk

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
        [ HH.text $ "💡 " <> hunk.explanation ]
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

renderSplitHunk :: forall m. DiffHunk -> H.ComponentHTML Action () m
renderSplitHunk hunk =
  HH.div
    [ HP.class_ (H.ClassName "diff-hunk-split") ]
    [ HH.div
        [ HP.class_ (H.ClassName "split-original") ]
        [ HH.h4_ [ HH.text "Original" ]
        , HH.div
            [ HP.class_ (H.ClassName "hunk-old") ]
            (mapWithIndex (\index line -> HH.div [ HP.class_ (H.ClassName "line") ] [ HH.text line ]) hunk.oldLines)
        ]
    , HH.div
        [ HP.class_ (H.ClassName "split-modified") ]
        [ HH.h4_ [ HH.text "Modified" ]
        , HH.div
            [ HP.class_ (H.ClassName "hunk-new") ]
            (mapWithIndex (\index line -> HH.div [ HP.class_ (H.ClassName "line") ] [ HH.text line ]) hunk.newLines)
        ]
    , HH.div
        [ HP.class_ (H.ClassName "hunk-explanation") ]
        [ HH.text $ "💡 " <> hunk.explanation ]
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

statusClass :: DiffStatus -> String
statusClass = case _ of
  Pending -> "pending"
  Accepted -> "accepted"
  Rejected -> "rejected"
  Modified -> "modified"

statusText :: DiffStatus -> String
statusText = case _ of
  Pending -> "Pending"
  Accepted -> "Accepted"
  Rejected -> "Rejected"
  Modified -> "Modified"

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
                        [ HH.text "×" ]
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
            , HE.onClick \_ -> pure unit
            ]
            [ HH.div
                [ HP.class_ (H.ClassName "modal-header") ]
                [ HH.h3_ [ HH.text $ "Preview: " <> file ]
                , HH.button
                    [ HP.class_ (H.ClassName "btn-close")
                    , HE.onClick \_ -> ClosePreview
                    ]
                    [ HH.text "×" ]
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
    H.modify_ \s ->
      { s
      | diffs = diffs
      , pendingCount = pendingCount
      }
  
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
    state <- H.get
    H.modify_ \s ->
      { s
      | diffs = map (\diff -> diff { hunks = map (\hunk -> hunk { status = Accepted }) diff.hunks }) s.diffs
      , pendingCount = 0
      }
  
  RejectAll -> do
    H.raise AllRejected
    state <- H.get
    H.modify_ \s ->
      { s
      | diffs = map (\diff -> diff { hunks = map (\hunk -> hunk { status = Rejected }) diff.hunks }) s.diffs
      , pendingCount = 0
      }
  
  OpenEditDialog hunkId -> do
    state <- H.get
    case findHunk hunkId state.diffs of
      Just { hunk } -> do
        -- Initialize edit content with new lines
        let content = String.joinWith "\n" hunk.newLines
        H.modify_ \s ->
          { s
          | editingHunk = Just hunkId
          , editContent = content
          }
      Nothing ->
        pure unit
  
  UpdateEditContent content -> do
    H.modify_ \s -> s { editContent = content }
  
  SaveEdit hunkId -> do
    state <- H.get
    let newLines = String.split (Pattern "\n") state.editContent
    -- Update the hunk with edited content
    H.modify_ \s ->
      { s
      | diffs = map (\diff -> diff { hunks = map (\hunk -> if hunk.id == hunkId then hunk { newLines = newLines, status = Modified } else hunk) diff.hunks }) s.diffs
      , editingHunk = Nothing
      , editContent = ""
      }
  
  CancelEdit -> do
    H.modify_ \s ->
      { s
      | editingHunk = Nothing
      , editContent = ""
      }
  
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
            H.modify_ \s ->
              { s
              | previewFile = Just file
              , previewContent = response.content
              }
          Left err -> do
            H.modify_ \s ->
              { s
              | previewFile = Just file
              , previewContent = Just ("Error loading file: " <> err.message)
              }
      Nothing -> do
        H.modify_ \s ->
          { s
          | previewFile = Just file
          , previewContent = Just ("Not connected to bridge server")
          }
  
  ClosePreview -> do
    H.modify_ \s ->
      { s
      | previewFile = Nothing
      , previewContent = Nothing
      }
  
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

-- | Handle component queries
handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  UpdateDiffsQuery diffs a -> do
    handleAction (UpdateDiffs diffs)
    pure (Just a)
  
  AcceptHunkQuery file hunkId a -> do
    handleAction (AcceptHunk hunkId)
    pure (Just a)
  
  RejectHunkQuery file hunkId a -> do
    handleAction (RejectHunk hunkId)
    pure (Just a)

-- Helper functions
countPending :: Array FileDiff -> Int
countPending diffs =
  foldl (\acc diff -> acc + length (filter (\h -> h.status == Pending) diff.hunks)) 0 diffs

findHunk :: String -> Array FileDiff -> Maybe { file :: String, hunk :: DiffHunk }
findHunk hunkId diffs =
  -- Search through all diffs and hunks to find matching hunkId
  Array.findMap searchInDiff diffs
  where
    searchInDiff :: FileDiff -> Maybe { file :: String, hunk :: DiffHunk }
    searchInDiff diff =
      Array.findMap (\hunk -> if hunk.id == hunkId then Just { file: diff.file, hunk } else Nothing) diff.hunks

