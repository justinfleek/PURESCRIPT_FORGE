-- | Export Dialog Component - Data Export and Sharing
-- |
-- | **What:** Provides comprehensive export functionality for sessions, analytics, recordings,
-- |         and settings in various formats (JSON, Markdown, HTML, CSV, PDF).
-- | **Why:** Enables users to export data for sharing, archiving, and external analysis.
-- | **How:** Renders export modal with format selection, options, preview, and download/copy
-- |         functionality. Supports multiple export types and formats.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Api.Bridge`: Export API calls
-- | - `Sidepanel.FFI.Download`: File download functionality
-- | - `Sidepanel.FFI.Clipboard`: Clipboard copy functionality
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Export.ExportDialog as ExportDialog
-- |
-- | -- In parent component:
-- | HH.slot _exportDialog unit ExportDialog.component
-- |   { visible: true, exportType: SessionExport "sess_abc123", wsClient: Just wsClient }
-- |   (case _ of
-- |     ExportDialog.ExportCompleted -> HandleExportCompleted
-- |     ExportDialog.ExportCancelled -> HandleExportCancelled)
-- | ```
-- |
-- | Based on spec 86-EXPORT-FUNCTIONALITY.md
module Sidepanel.Components.Export.ExportDialog where

import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Class (liftEffect)
import Effect.Aff.Class (class MonadAff)
import Effect.Aff (Aff)
import Sidepanel.WebSocket.Client as WS
import Sidepanel.Api.Bridge as Bridge
import Sidepanel.FFI.Download as Download
import Sidepanel.FFI.Clipboard as Clipboard

-- | Export type
data ExportType
  = SessionExport String  -- sessionId
  | AnalyticsExport
  | RecordingExport String  -- recordingId
  | SettingsExport
  | DiffExport String  -- diffId

derive instance eqExportType :: Eq ExportType

-- | Export format
data ExportFormat
  = MarkdownFormat
  | JSONFormat
  | HTMLFormat
  | CSVFormat
  | PDFFormat
  | APIFormat

derive instance eqExportFormat :: Eq ExportFormat

-- | Export options
type ExportOptions =
  { includeMessageContent :: Boolean
  , includeTimestamps :: Boolean
  , includeTokenCounts :: Boolean
  , includeToolDetails :: Boolean
  , includeFileContents :: Boolean
  , includeCostBreakdown :: Boolean
  , messageRange :: Maybe { from :: Int, to :: Int }
  }

-- | Component input
type Input =
  { visible :: Boolean
  , exportType :: Maybe ExportType
  , wsClient :: Maybe WS.WSClient
  }

-- | Component state
type State =
  { visible :: Boolean
  , exportType :: Maybe ExportType
  , format :: ExportFormat
  , options :: ExportOptions
  , preview :: Maybe String
  , isExporting :: Boolean
  , wsClient :: Maybe WS.WSClient
  }

-- | Component actions
data Action
  = Initialize
  = Receive Input
  | SetFormat ExportFormat
  | ToggleOption String
  | SetMessageRange (Maybe { from :: Int, to :: Int })
  | GeneratePreview
  | ExportToFile
  | CopyToClipboard
  | Close

-- | Component output
data Output
  = ExportCompleted String  -- filename
  | ExportCancelled

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      { visible: input.visible
      , exportType: input.exportType
      , format: MarkdownFormat
      , options:
          { includeMessageContent: true
          , includeTimestamps: true
          , includeTokenCounts: true
          , includeToolDetails: false
          , includeFileContents: false
          , includeCostBreakdown: true
          , messageRange: Nothing
          }
      , preview: Nothing
      , isExporting: false
      , wsClient: input.wsClient
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      , initialize = Just Initialize
      }
  }

-- | Render component
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  if state.visible then
    HH.div
      [ HP.class_ (H.ClassName "export-dialog-overlay")
      , HE.onClick \_ -> Close
      ]
      [ HH.div
          [ HP.class_ (H.ClassName "export-dialog")
          , HE.onClick \_ -> pure unit
          ]
          [ renderHeader
          , renderFormatSelection state
          , renderOptions state
          , renderPreview state
          , renderActions state
          ]
      ]
  else
    HH.text ""

-- | Render header
renderHeader :: forall m. H.ComponentHTML Action () m
renderHeader =
  HH.header
    [ HP.class_ (H.ClassName "export-dialog__header") ]
    [ HH.h2_ [ HH.text "EXPORT" ]
    , HH.button
        [ HP.class_ (H.ClassName "export-dialog__close")
        , HE.onClick \_ -> Close
        ]
        [ HH.text "✕" ]
    ]

-- | Render format selection
renderFormatSelection :: forall m. State -> H.ComponentHTML Action () m
renderFormatSelection state =
  HH.div
    [ HP.class_ (H.ClassName "format-selection") ]
    [ HH.h3_ [ HH.text "Format" ]
    , HH.select
        [ HP.class_ (H.ClassName "format-select")
        , HE.onValueChange \v -> SetFormat (parseFormat v)
        ]
        [ HH.option [ HP.value "markdown" ] [ HH.text "Markdown" ]
        , HH.option [ HP.value "json" ] [ HH.text "JSON" ]
        , HH.option [ HP.value "html" ] [ HH.text "HTML Report" ]
        , HH.option [ HP.value "csv" ] [ HH.text "CSV" ]
        , HH.option [ HP.value "pdf" ] [ HH.text "PDF Report" ]
        ]
    ]

-- | Render options
renderOptions :: forall m. State -> H.ComponentHTML Action () m
renderOptions state =
  HH.div
    [ HP.class_ (H.ClassName "export-options") ]
    [ HH.h3_ [ HH.text "OPTIONS" ]
    , HH.div
        [ HP.class_ (H.ClassName "options-list") ]
        [ renderCheckbox "Include message content" state.options.includeMessageContent "includeMessageContent"
        , renderCheckbox "Include timestamps" state.options.includeTimestamps "includeTimestamps"
        , renderCheckbox "Include token counts" state.options.includeTokenCounts "includeTokenCounts"
        , renderCheckbox "Include tool execution details" state.options.includeToolDetails "includeToolDetails"
        , renderCheckbox "Include file contents (large)" state.options.includeFileContents "includeFileContents"
        , renderCheckbox "Include cost breakdown" state.options.includeCostBreakdown "includeCostBreakdown"
        ]
    ]

-- | Render checkbox
renderCheckbox :: forall m. String -> Boolean -> String -> H.ComponentHTML Action () m
renderCheckbox label checked optionId =
  HH.label
    [ HP.class_ (H.ClassName "option-checkbox") ]
    [ HH.input
        [ HP.type_ HP.InputCheckbox
        , HP.checked checked
        , HE.onChecked \_ -> ToggleOption optionId
        ]
    , HH.text label
    ]

-- | Render preview
renderPreview :: forall m. State -> H.ComponentHTML Action () m
renderPreview state =
  case state.preview of
    Just preview ->
      HH.div
        [ HP.class_ (H.ClassName "export-preview") ]
        [ HH.h3_ [ HH.text "PREVIEW" ]
        , HH.pre
            [ HP.class_ (H.ClassName "preview-content") ]
            [ HH.text preview ]
        ]
    Nothing ->
      HH.div
        [ HP.class_ (H.ClassName "export-preview-empty") ]
        [ HH.text "Click 'Generate Preview' to see export preview" ]

-- | Render actions
renderActions :: forall m. State -> H.ComponentHTML Action () m
renderActions state =
  HH.div
    [ HP.class_ (H.ClassName "export-actions") ]
    [ HH.button
        [ HP.class_ (H.ClassName "btn btn--secondary")
        , HE.onClick \_ -> Close
        ]
        [ HH.text "Cancel" ]
    , HH.button
        [ HP.class_ (H.ClassName "btn btn--secondary")
        , HE.onClick \_ -> GeneratePreview
        ]
        [ HH.text "Generate Preview" ]
    , HH.button
        [ HP.class_ (H.ClassName "btn btn--primary")
        , HP.disabled state.isExporting
        , HE.onClick \_ -> CopyToClipboard
        ]
        [ HH.text "Copy to Clipboard" ]
    , HH.button
        [ HP.class_ (H.ClassName "btn btn--primary")
        , HP.disabled state.isExporting
        , HE.onClick \_ -> ExportToFile
        ]
        [ HH.text $ if state.isExporting then "Exporting..." else "Download File" ]
    ]

-- | Parse format string
parseFormat :: String -> ExportFormat
parseFormat = case _ of
  "markdown" -> MarkdownFormat
  "json" -> JSONFormat
  "html" -> HTMLFormat
  "csv" -> CSVFormat
  "pdf" -> PDFFormat
  "api" -> APIFormat
  _ -> MarkdownFormat

-- | Format to string
formatToString :: ExportFormat -> String
formatToString = case _ of
  MarkdownFormat -> "markdown"
  JSONFormat -> "json"
  HTMLFormat -> "html"
  CSVFormat -> "csv"
  PDFFormat -> "pdf"
  APIFormat -> "api"

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    handleAction GeneratePreview
  
  Receive input -> do
    H.modify_ _
      { visible = input.visible
      , exportType = input.exportType
      , wsClient = input.wsClient
      }
    if input.visible then
      handleAction GeneratePreview
    else
      pure unit
  
  SetFormat format -> do
    H.modify_ _ { format = format }
    handleAction GeneratePreview
  
  ToggleOption optionId -> do
    state <- H.get
    let newOptions = case optionId of
          "includeMessageContent" -> state.options { includeMessageContent = not state.options.includeMessageContent }
          "includeTimestamps" -> state.options { includeTimestamps = not state.options.includeTimestamps }
          "includeTokenCounts" -> state.options { includeTokenCounts = not state.options.includeTokenCounts }
          "includeToolDetails" -> state.options { includeToolDetails = not state.options.includeToolDetails }
          "includeFileContents" -> state.options { includeFileContents = not state.options.includeFileContents }
          "includeCostBreakdown" -> state.options { includeCostBreakdown = not state.options.includeCostBreakdown }
          _ -> state.options
    H.modify_ _ { options = newOptions }
  
  SetMessageRange range -> do
    H.modify_ _ { options { messageRange = range } }
    handleAction GeneratePreview
  
  GeneratePreview -> do
    state <- H.get
    case state.exportType, state.wsClient of
      Just (SessionExport sessionId), Just client -> do
        -- Generate preview via Bridge API
        result <- liftEffect $ Bridge.exportSession client
          { sessionId: sessionId
          , format: formatToString state.format
          , includeTimeline: Just state.options.includeTimestamps
          }
        case result of
          Right response -> do
            -- Show first 500 chars as preview
            let preview = String.take 500 response.data
            H.modify_ _ { preview = Just preview }
          Left _ -> pure unit
      _, _ -> pure unit
  
  ExportToFile -> do
    state <- H.get
    H.modify_ _ { isExporting = true }
    case state.exportType, state.wsClient of
      Just (SessionExport sessionId), Just client -> do
        result <- liftEffect $ Bridge.exportSession client
          { sessionId: sessionId
          , format: formatToString state.format
          , includeTimeline: Just state.options.includeTimestamps
          }
        case result of
          Right response -> do
            liftEffect $ Download.downloadFile response.data response.filename
            H.modify_ _ { isExporting = false, visible = false }
            H.raise (ExportCompleted response.filename)
          Left _ -> do
            H.modify_ _ { isExporting = false }
      _, _ -> do
        H.modify_ _ { isExporting = false }
  
  CopyToClipboard -> do
    state <- H.get
    case state.preview of
      Just preview -> do
        liftEffect $ Clipboard.copyToClipboard preview
        H.modify_ _ { visible = false }
        H.raise (ExportCompleted "clipboard")
      Nothing -> pure unit
  
  Close -> do
    H.modify_ _ { visible = false, preview = Nothing }
    H.raise ExportCancelled
