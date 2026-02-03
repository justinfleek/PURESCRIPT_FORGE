-- | File Context View Component - AI Context Window Visibility
-- |
-- | **What:** Displays files currently in the AI context window, organized by directory.
-- |         Shows token usage per file, context budget, and provides management tools
-- |         (add/remove files, preview, filter). Shows AI recommendations for files to add.
-- | **Why:** Enables users to understand what files are being sent to the AI, manage
-- |         context window size, and optimize token usage. Critical for debugging context
-- |         issues and controlling costs.
-- | **How:** Groups files by directory, displays token counts and budget usage, provides
-- |         filtering and search, and allows adding/removing files. Loads file list from
-- |         Bridge Server via WebSocket.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.WebSocket.Client`: WebSocket communication
-- | - `Sidepanel.Api.Bridge`: Bridge API methods for file context operations
-- |
-- | **Mathematical Foundation:**
-- | - **Context Budget:** Calculated as `percentage = (used / total) * 100`. Default total
-- |   is 80,000 tokens.
-- | - **Directory Grouping:** Files are grouped by directory path (extracted from file path
-- |   by finding last "/").
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.FileContextView as FileContextView
-- |
-- | -- In parent component:
-- | HH.slot _fileContext unit FileContextView.component
-- |   { wsClient: wsClient }
-- |   (case _ of
-- |     FileContextView.FilesRemoved paths -> HandleFilesRemoved paths
-- |     FileContextView.FilesAdded paths -> HandleFilesAdded paths
-- |     FileContextView.ContextRefreshed -> HandleContextRefreshed)
-- | ```
-- |
-- | Spec 58: AI Context Visibility - shows files in context window
module Sidepanel.Components.FileContextView where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Data.Array (filter, mapWithIndex, length, snoc, foldl)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), contains, toLower)
import Data.Array as Array
import Data.String as String
import Data.Int as Int
import Data.Either (Either(..))
import Sidepanel.WebSocket.Client as WS
import Sidepanel.Api.Bridge as Bridge
import Sidepanel.Components.CodeSelection as CodeSelection

-- | File in context
type FileInContext =
  { path :: String
  , tokens :: Int
  , readAt :: Number -- timestamp
  , status :: FileStatus
  , language :: String
  , size :: Int -- bytes
  }

-- | File status
data FileStatus
  = Active -- Currently in context
  | Stale -- In context but not recently referenced
  | Recommended -- Should be added to context

derive instance eqFileStatus :: Eq FileStatus

-- | Directory grouping
type DirectoryGroup =
  { path :: String
  , files :: Array FileInContext
  , totalTokens :: Int
  }

-- | Component state
type State =
  { files :: Array FileInContext
  , groupedFiles :: Array DirectoryGroup
  , selectedFiles :: Array String -- file paths
  , contextBudget :: ContextBudget
  , filterQuery :: String
  , showStale :: Boolean
  , showRecommended :: Boolean
  , wsClient :: Maybe WS.WSClient
  , previewFile :: Maybe String -- file being previewed
  , previewContent :: Maybe String -- preview file content
  }

-- | Context budget
type ContextBudget =
  { used :: Int
  , total :: Int
  , percentage :: Number
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
  | OpenPreview String -- file path
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

-- | File Context View component
component :: forall q m. MonadAff m => H.Component q Input Output m
component =
  H.mkComponent
    { initialState: \input -> initialState { wsClient = input.wsClient }
    , render
    , eval: H.mkEval $ H.defaultEval
        { handleAction = handleAction
        , initialize = Just Initialize
        }
    }

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

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "file-context-view") ]
    [ renderHeader state
    , renderBudgetBar state.contextBudget
    , renderFileGroups state.groupedFiles state.selectedFiles
    , renderRecommendations state.files
    , renderQuickActions
    , renderPreviewModal state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.div
    [ HP.class_ (H.ClassName "file-context-header") ]
    [ HH.h3_ [ HH.text "File Context" ]
    , HH.div
        [ HP.class_ (H.ClassName "header-controls") ]
        [ HH.input
            [ HP.class_ (H.ClassName "filter-input")
            , HP.type_ HP.InputText
            , HP.placeholder "Filter files..."
            , HP.value state.filterQuery
            , HE.onValueInput UpdateFilter
            ]
        , HH.button
            [ HP.class_ (H.ClassName "btn-refresh")
            , HE.onClick \_ -> RefreshContext
            ]
            [ HH.text "Refresh" ]
        , HH.button
            [ HP.class_ (H.ClassName "btn-clear-all")
            , HE.onClick \_ -> ClearAll
            ]
            [ HH.text "Clear All" ]
        ]
    ]

renderBudgetBar :: forall m. ContextBudget -> H.ComponentHTML Action () m
renderBudgetBar budget =
  HH.div
    [ HP.class_ (H.ClassName "context-budget-bar") ]
    [ HH.div
        [ HP.class_ (H.ClassName "budget-label") ]
        [ HH.text $ "Context Budget: " <> show budget.percentage <> "% (" <> show budget.used <> " / " <> show budget.total <> " tokens)" ]
    , HH.div
        [ HP.class_ (H.ClassName "budget-progress") ]
        [ HH.div
            [ HP.class_ (H.ClassName "budget-fill")
            , HP.style $ "width: " <> show budget.percentage <> "%"
            ]
            []
        ]
    ]

renderFileGroups :: forall m. Array DirectoryGroup -> Array String -> H.ComponentHTML Action () m
renderFileGroups groups selected =
  HH.div
    [ HP.class_ (H.ClassName "file-groups") ]
    (mapWithIndex (\index group -> renderDirectoryGroup index group selected) groups)

renderDirectoryGroup :: forall m. Int -> DirectoryGroup -> Array String -> H.ComponentHTML Action () m
renderDirectoryGroup index group selected =
  HH.div
    [ HP.class_ (H.ClassName "directory-group") ]
    [ HH.div
        [ HP.class_ (H.ClassName "directory-header") ]
        [ HH.text $ group.path <> " - " <> show (length group.files) <> " files, " <> show group.totalTokens <> " tokens" ]
    , HH.div
        [ HP.class_ (H.ClassName "directory-files") ]
        (mapWithIndex (\fileIndex file -> renderFile fileIndex file selected) group.files)
    ]

renderFile :: forall m. Int -> FileInContext -> Array String -> H.ComponentHTML Action () m
renderFile index file selected =
  let isSelected = Array.elem file.path selected
  in
    HH.div
      [ HP.class_ (H.ClassName $ "file-item " <> if isSelected then "selected" else "")
      , HE.onClick \_ -> ToggleFileSelection file.path
      ]
      [ HH.input
          [ HP.type_ HP.InputCheckbox
          , HP.checked isSelected
          , HE.onChecked \_ -> ToggleFileSelection file.path
          ]
    , HH.span
        [ HP.class_ (H.ClassName "file-icon") ]
        [ HH.text "📄" ]
    , HH.span
        [ HP.class_ (H.ClassName "file-path") ]
        [ HH.text file.path ]
    , HH.span
        [ HP.class_ (H.ClassName "file-tokens") ]
        [ HH.text $ show file.tokens <> " tk" ]
    , HH.span
        [ HP.class_ (H.ClassName "file-time") ]
        [ HH.text $ "Read " <> show file.readAt ]
    , HH.button
        [ HP.class_ (H.ClassName "btn-remove")
        , HE.onClick \e -> do
            H.stopPropagation e
            RemoveSelected
        ]
        [ HH.text "−" ]
    , HH.button
        [ HP.class_ (H.ClassName "btn-preview")
        , HE.onClick \e -> do
            H.stopPropagation e
            OpenPreview file.path
        ]
        [ HH.text "👁" ]
    ]

renderRecommendations :: forall m. Array FileInContext -> H.ComponentHTML Action () m
renderRecommendations files =
  let recommended = filter (\f -> f.status == Recommended) files
  in
    if length recommended > 0 then
      HH.div
        [ HP.class_ (H.ClassName "recommendations") ]
        [ HH.h4_ [ HH.text "AI Recommendations" ]
        , HH.div
            [ HP.class_ (H.ClassName "recommended-files") ]
            (map (\file -> renderRecommendedFile file) recommended)
        ]
    else
      HH.text ""

renderRecommendedFile :: forall m. FileInContext -> H.ComponentHTML Action () m
renderRecommendedFile file =
  HH.div
    [ HP.class_ (H.ClassName "recommended-file") ]
    [ HH.span
        [ HP.class_ (H.ClassName "recommendation-icon") ]
        [ HH.text "⚡" ]
    , HH.span
        [ HP.class_ (H.ClassName "recommended-path") ]
        [ HH.text file.path ]
    , HH.span
        [ HP.class_ (H.ClassName "recommended-tokens") ]
        [ HH.text $ "~" <> show file.tokens <> " tk" ]
    , HH.button
        [ HP.class_ (H.ClassName "btn-add")
        , HE.onClick \_ -> AddRecommended file.path
        ]
        [ HH.text "+ Add to Context" ]
    ]

renderQuickActions :: forall m. H.ComponentHTML Action () m
renderQuickActions =
  HH.div
    [ HP.class_ (H.ClassName "quick-actions") ]
    [ HH.button
        [ HP.class_ (H.ClassName "btn-add-files") ]
        [ HH.text "+ Add Files..." ]
    , HH.button
        [ HP.class_ (H.ClassName "btn-add-directory") ]
        [ HH.text "📁 Add Directory..." ]
    , HH.button
        [ HP.class_ (H.ClassName "btn-save-preset") ]
        [ HH.text "💾 Save as Preset..." ]
    ]

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Load files from bridge server
    state <- H.get
    case state.wsClient of
      Just client -> do
        result <- H.liftAff $ Bridge.listFilesInContext client { sessionId: Nothing, filter: Nothing }
        case result of
          Right response -> do
            H.modify_ \s ->
              { s
              | files = response.files
              , groupedFiles = groupFilesByDirectory response.files
              , contextBudget =
                  { used: response.contextBudget.used
                  , total: response.contextBudget.total
                  , percentage: if response.contextBudget.total > 0
                      then (toNumber response.contextBudget.used / toNumber response.contextBudget.total) * 100.0
                      else 0.0
                  }
              }
          Left _ -> pure unit -- Handle error silently on init
      Nothing -> pure unit -- No client available
  
  UpdateFiles files -> do
    H.modify_ \s ->
      { s
      | files = files
      , groupedFiles = groupFilesByDirectory files
      , contextBudget = calculateBudget files s.contextBudget.total
      }
  
  ToggleFileSelection path -> do
    state <- H.get
    let newSelected = if Array.elem path state.selectedFiles then
          filter (\p -> p /= path) state.selectedFiles
        else
          snoc state.selectedFiles path
    H.modify_ \s -> s { selectedFiles = newSelected }
  
  SelectAll -> do
    state <- H.get
    let allPaths = map _.path state.files
    H.modify_ \s -> s { selectedFiles = allPaths }
  
  DeselectAll -> do
    H.modify_ \s -> s { selectedFiles = [] }
  
  RemoveSelected -> do
    state <- H.get
    if length state.selectedFiles > 0 then do
      H.raise (FilesRemoved state.selectedFiles)
      H.modify_ \s ->
        { s
        | files = filter (\f -> not $ Array.elem f.path state.selectedFiles) s.files
        , selectedFiles = []
        }
      -- Recalculate groups and budget
      updatedState <- H.get
      H.modify_ \s ->
        { s
        | groupedFiles = groupFilesByDirectory updatedState.files
        , contextBudget = calculateBudget updatedState.files s.contextBudget.total
        }
    else
      pure unit
  
  AddRecommended path -> do
    state <- H.get
    case state.wsClient of
      Just client -> do
        result <- H.liftAff $ Bridge.addFileToContext client { path, sessionId: Nothing }
        case result of
          Right response -> do
            H.raise (FilesAdded [path])
            -- Update context budget
            H.modify_ \s ->
              { s
              | contextBudget =
                  { used: response.contextBudget.used
                  , total: response.contextBudget.total
                  , percentage: if response.contextBudget.total > 0
                      then (toNumber response.contextBudget.used / toNumber response.contextBudget.total) * 100.0
                      else 0.0
                  }
              }
          Left err -> pure unit -- Handle error (could show notification)
      Nothing -> pure unit -- No client available
  
  UpdateFilter query -> do
    H.modify_ \s -> s { filterQuery = query }
    -- Filter files client-side based on query
    state <- H.get
    let filtered = if query == "" then
          state.files
        else
          filter (\f -> contains (Pattern $ toLower query) (toLower f.path)) state.files
    H.modify_ \s -> s { groupedFiles = groupFilesByDirectory filtered }
  
  ToggleShowStale -> do
    H.modify_ \s -> s { showStale = not s.showStale }
  
  ToggleShowRecommended -> do
    H.modify_ \s -> s { showRecommended = not s.showRecommended }
  
  RefreshContext -> do
    state <- H.get
    case state.wsClient of
      Just client -> do
        result <- H.liftAff $ Bridge.listFilesInContext client { sessionId: Nothing, filter: Nothing }
        case result of
          Right response -> do
            H.raise ContextRefreshed
            H.modify_ \s ->
              { s
              | files = response.files
              , groupedFiles = groupFilesByDirectory response.files
              , contextBudget =
                  { used: response.contextBudget.used
                  , total: response.contextBudget.total
                  , percentage: if response.contextBudget.total > 0
                      then (toNumber response.contextBudget.used / toNumber response.contextBudget.total) * 100.0
                      else 0.0
                  }
              }
          Left err -> pure unit -- Handle error
      Nothing -> pure unit -- No client available
  
  ClearAll -> do
    state <- H.get
    let allPaths = map _.path state.files
    H.raise (FilesRemoved allPaths)
    H.modify_ \s ->
      { s
      | files = []
      , groupedFiles = []
      , selectedFiles = []
      , contextBudget = s.contextBudget { used = 0, percentage = 0.0 }
      }
  
  OpenPreview file -> do
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
  
  HandleCodeCopied code -> do
    -- Code was copied to clipboard - could show notification
    pure unit
  
  HandleCodeAddedToChat code -> do
    -- Code was added to chat (copied with formatting) - could show notification
    pure unit
  
  NoOp ->
    pure unit

-- | Group files by directory
groupFilesByDirectory :: Array FileInContext -> Array DirectoryGroup
groupFilesByDirectory files =
  let
    -- Group files by directory path
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
      percentage = if total > 0 then (toNumber used / toNumber total) * 100.0 else 0.0
  in
    { used
    , total
    , percentage
    }

-- Helper: Convert Int to Number
toNumber :: Int -> Number
toNumber = Int.toNumber

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
                    [ HH.text "×" ]
                ]
            , HH.div
                [ HP.class_ (H.ClassName "modal-body") ]
                [ case state.previewContent of
                    Just content ->
                      let
                        lines = String.split (Pattern "\n") content
                        language = detectLanguage file
                      in
                        HH.slot (H.Slot unit) unit CodeSelection.component
                          { codeLines: lines
                          , filePath: Just file
                          , language: language
                          }
                          (case _ of
                            CodeSelection.Copied code -> HandleCodeCopied code
                            CodeSelection.AddedToChat code -> HandleCodeAddedToChat code
                            CodeSelection.SelectionChanged _ -> NoOp)
                    Nothing ->
                      HH.text "Loading..."
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
