-- | Code Component
-- | Migrated from: forge-dev/packages/ui/src/components/code.tsx
-- | Original lines: 498
-- |
-- | Code viewer with syntax highlighting and line selection support.
-- | Uses pierre/diffs File renderer for code display.
-- |
-- | Data Attributes:
-- | - data-component="code": Root element
-- | - data-line: Line number marker
-- | - data-code: Code content area
-- | - data-deletions: Deletion marker
-- | - data-comment-selected: Lines selected for comment
-- | - data-color-scheme: Theme color scheme

module UI.Components.Code
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , SelectionSide(..)
  , SelectedLineRange
  , FileContents
  , defaultInput
  ) where

import Prelude

import Data.Array (filter, length)
import Data.Foldable (for_)
import Data.Int (floor)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Web.Event.Event as Event
import Web.HTML as HTML
import Web.HTML.Window as Window
import Web.UIEvent.MouseEvent as ME

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Selection side type
data SelectionSide
  = Additions
  | Deletions

derive instance eqSelectionSide :: Eq SelectionSide

sideToString :: SelectionSide -> String
sideToString Additions = "additions"
sideToString Deletions = "deletions"

parseSide :: String -> Maybe SelectionSide
parseSide "additions" = Just Additions
parseSide "deletions" = Just Deletions
parseSide _ = Nothing

-- | Selected line range
type SelectedLineRange =
  { start :: Int
  , end :: Int
  , side :: Maybe SelectionSide
  , endSide :: Maybe SelectionSide
  }

-- | File contents type
type FileContents =
  { name :: Maybe String
  , contents :: String
  , cacheKey :: Maybe String
  }

-- | Line annotation type
type LineAnnotation =
  { lineNumber :: Int
  , side :: Maybe SelectionSide
  }

-- | Code component input props
type Input =
  { file :: FileContents
  , annotations :: Array LineAnnotation
  , selectedLines :: Maybe SelectedLineRange
  , commentedLines :: Array SelectedLineRange
  , enableLineSelection :: Boolean
  , overflow :: String  -- "scroll" | "auto"
  , disableLineNumbers :: Boolean
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { file: { name: Nothing, contents: "", cacheKey: Nothing }
  , annotations: []
  , selectedLines: Nothing
  , commentedLines: []
  , enableLineSelection: false
  , overflow: "auto"
  , disableLineNumbers: false
  , className: Nothing
  }

-- | Output events
data Output
  = Rendered
  | LineSelectionEnd (Maybe SelectedLineRange)

-- | Queries for external control
data Query a
  = SetSelectedLines (Maybe SelectedLineRange) a
  | GetSelectedLines (Maybe SelectedLineRange -> a)
  | Refresh a

-- | Internal state
type State =
  { input :: Input
  , renderToken :: Int
  , lastSelection :: Maybe SelectedLineRange
  , dragStart :: Maybe Int
  , dragEnd :: Maybe Int
  , dragMoved :: Boolean
  }

-- | Internal actions
data Action
  = Initialize
  | Finalize
  | Receive Input
  | HandleMouseDown ME.MouseEvent
  | HandleMouseMove ME.MouseEvent
  | HandleMouseUp
  | HandleSelectionChange
  | RenderComplete

-- | Slot type for parent components
type Slot id = H.Slot Query Output id

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      , finalize = Just Finalize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { input
  , renderToken: 0
  , lastSelection: input.selectedLines
  , dragStart: Nothing
  , dragEnd: Nothing
  , dragMoved: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    ([ HP.ref (H.RefLabel "container")
    , HP.attr (HH.AttrName "data-component") "code"
    , HP.attr (HH.AttrName "style") styleVariables
    ] <> classAttr state.input.className
      <> mouseHandlers state.input.enableLineSelection)
    []
  where
    mouseHandlers :: Boolean -> Array (HP.IProp _ Action)
    mouseHandlers false = []
    mouseHandlers true = 
      [ HE.onMouseDown HandleMouseDown
      , HE.onMouseMove HandleMouseMove
      ]

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    state <- H.get
    -- Initial render
    renderFile state.input
    -- Set up color scheme monitoring
    liftEffect setupColorSchemeMonitor
    -- Set up global mouse up handler
    when state.input.enableLineSelection do
      liftEffect $ setupGlobalMouseUp

  Finalize -> do
    -- Cleanup file renderer
    liftEffect cleanupFile
    -- Cleanup color scheme monitor
    liftEffect cleanupColorSchemeMonitor

  Receive newInput -> do
    state <- H.get
    -- Check if file content changed
    let fileChanged = 
          state.input.file.contents /= newInput.file.contents ||
          state.input.file.name /= newInput.file.name
    
    when fileChanged do
      H.modify_ _ { renderToken = state.renderToken + 1 }
      renderFile newInput
    
    -- Update selected lines
    when (state.input.selectedLines /= newInput.selectedLines) do
      H.modify_ _ { lastSelection = newInput.selectedLines }
      liftEffect $ applySelection newInput.selectedLines (lineCount newInput.file.contents)
    
    -- Update commented lines
    when (state.input.commentedLines /= newInput.commentedLines) do
      liftEffect $ applyCommentedLines newInput.commentedLines
    
    H.modify_ _ { input = newInput }

  HandleMouseDown me -> do
    state <- H.get
    when state.input.enableLineSelection do
      let button = ME.button me
      when (button == 0) do
        mLineInfo <- liftEffect $ lineFromMouseEvent me
        case mLineInfo of
          { line: Just line, numberColumn: false } -> do
            H.modify_ _ 
              { dragStart = Just line
              , dragEnd = Just line
              , dragMoved = false
              }
          _ -> pure unit

  HandleMouseMove me -> do
    state <- H.get
    when state.input.enableLineSelection do
      case state.dragStart of
        Nothing -> pure unit
        Just _ -> do
          -- Check if mouse button still pressed
          let buttons = ME.buttons me
          if buttons == 0
            then H.modify_ _ { dragStart = Nothing, dragEnd = Nothing, dragMoved = false }
            else do
              mLineInfo <- liftEffect $ lineFromMouseEvent me
              case mLineInfo.line of
                Nothing -> pure unit
                Just line -> do
                  H.modify_ _ { dragEnd = Just line, dragMoved = true }
                  updateDragSelection

  HandleMouseUp -> do
    state <- H.get
    when state.input.enableLineSelection do
      case state.dragStart of
        Nothing -> pure unit
        Just startLine -> do
          if not state.dragMoved
            then do
              -- Single click - select single line
              let range = { start: startLine, end: startLine, side: Nothing, endSide: Nothing }
              H.modify_ _ { lastSelection = Just range }
              liftEffect $ applySelection (Just range) (lineCount state.input.file.contents)
              H.raise (LineSelectionEnd (Just range))
            else do
              -- Drag complete
              updateDragSelection
              newState <- H.get
              H.raise (LineSelectionEnd newState.lastSelection)
          
          H.modify_ _ { dragStart = Nothing, dragEnd = Nothing, dragMoved = false }

  HandleSelectionChange -> do
    state <- H.get
    when state.input.enableLineSelection do
      -- Update selection based on DOM selection
      liftEffect updateSelectionFromDOM

  RenderComplete -> do
    state <- H.get
    -- Apply selection after render
    liftEffect $ applySelection state.lastSelection (lineCount state.input.file.contents)
    -- Apply commented lines
    liftEffect $ applyCommentedLines state.input.commentedLines
    -- Notify rendered
    H.raise Rendered

-- | Update drag selection
updateDragSelection :: forall m. MonadAff m => H.HalogenM State Action () Output m Unit
updateDragSelection = do
  state <- H.get
  case state.dragStart, state.dragEnd of
    Just start, Just end -> do
      let range = { start, end, side: Nothing, endSide: Nothing }
      H.modify_ _ { lastSelection = Just range }
      liftEffect $ applySelection (Just range) (lineCount state.input.file.contents)
    _, _ -> pure unit

-- | Render file using FFI
renderFile :: forall m. MonadAff m => Input -> H.HalogenM State Action () Output m Unit
renderFile input = do
  mContainer <- H.getHTMLElementRef (H.RefLabel "container")
  for_ mContainer \container -> do
    liftEffect $ renderFileFFI container input
    -- Schedule render complete
    liftEffect $ scheduleRenderComplete (handleAction RenderComplete)
  where
    handleAction :: Action -> H.HalogenM State Action () Output m Unit
    handleAction = pure <<< const unit

-- | Count lines in content
lineCount :: String -> Int
lineCount text =
  let lines = String.split (String.Pattern "\n") text
      len = length lines
      endsWithNewline = String.takeRight 1 text == "\n"
  in max 1 (if endsWithNewline then len - 1 else len)

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetSelectedLines range a -> do
    state <- H.get
    H.modify_ _ { lastSelection = range }
    liftEffect $ applySelection range (lineCount state.input.file.contents)
    pure (Just a)
  
  GetSelectedLines reply -> do
    state <- H.get
    pure (Just (reply state.lastSelection))
  
  Refresh a -> do
    state <- H.get
    renderFile state.input
    pure (Just a)

-- ═══════════════════════════════════════════════════════════════════════════════
-- FFI (Minimal - only true DOM operations)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Style variables from pierre
foreign import styleVariables :: String

-- | Render file using pierre/diffs File renderer
-- | Takes container element and input, renders into shadow DOM
foreign import renderFileFFI :: forall a. a -> Input -> Effect Unit

-- | Cleanup file renderer
foreign import cleanupFile :: Effect Unit

-- | Apply selection to rendered lines
foreign import applySelection :: Maybe SelectedLineRange -> Int -> Effect Unit

-- | Apply commented lines styling
foreign import applyCommentedLines :: Array SelectedLineRange -> Effect Unit

-- | Setup color scheme monitoring (MutationObserver)
foreign import setupColorSchemeMonitor :: Effect Unit

-- | Cleanup color scheme monitor
foreign import cleanupColorSchemeMonitor :: Effect Unit

-- | Setup global mouseup handler
foreign import setupGlobalMouseUp :: Effect Unit

-- | Schedule render complete callback
foreign import scheduleRenderComplete :: Effect Unit -> Effect Unit

-- | Get line info from mouse event
foreign import lineFromMouseEvent :: ME.MouseEvent -> Effect { line :: Maybe Int, numberColumn :: Boolean }

-- | Update selection from DOM selection API
foreign import updateSelectionFromDOM :: Effect Unit
