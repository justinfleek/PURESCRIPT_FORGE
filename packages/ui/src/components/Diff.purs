-- | Diff Component
-- | Migrated from: forge-dev/packages/ui/src/components/diff.tsx
-- | Original lines: 613
-- |
-- | Diff viewer component using pierre/diffs FileDiff renderer.
-- | Supports unified and split views with line selection.
-- |
-- | Data Attributes:
-- | - data-component="diff": Root element
-- | - data-line: Line number
-- | - data-alt-line: Alternative line number
-- | - data-line-type: Line change type (change-deletion, change-addition)
-- | - data-code: Code block
-- | - data-deletions: Deletion side marker
-- | - data-diffs: Diffs container
-- | - data-type: Diff type (split/unified)
-- | - data-comment-selected: Selected for comment
-- | - data-line-annotation: Line annotation
-- | - data-color-scheme: Theme color scheme

module UI.Components.Diff
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , SelectionSide(..)
  , SelectedLineRange
  , FileInfo
  , DiffStyle(..)
  , defaultInput
  ) where

import Prelude

import Data.Array (length)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Web.UIEvent.MouseEvent as ME

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES (shared with Code.purs)
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

-- | Diff style
data DiffStyle
  = Unified
  | Split

derive instance eqDiffStyle :: Eq DiffStyle

diffStyleToString :: DiffStyle -> String
diffStyleToString Unified = "unified"
diffStyleToString Split = "split"

-- | Selected line range
type SelectedLineRange =
  { start :: Int
  , end :: Int
  , side :: Maybe SelectionSide
  , endSide :: Maybe SelectionSide
  }

-- | File info for diff
type FileInfo =
  { name :: Maybe String
  , contents :: String
  , cacheKey :: Maybe String
  }

-- | Line annotation type
type LineAnnotation =
  { lineNumber :: Int
  , side :: Maybe SelectionSide
  }

-- | Diff component input props
type Input =
  { before :: Maybe FileInfo
  , after :: Maybe FileInfo
  , diffStyle :: DiffStyle
  , annotations :: Array LineAnnotation
  , selectedLines :: Maybe SelectedLineRange
  , commentedLines :: Array SelectedLineRange
  , enableLineSelection :: Boolean
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { before: Nothing
  , after: Nothing
  , diffStyle: Unified
  , annotations: []
  , selectedLines: Nothing
  , commentedLines: []
  , enableLineSelection: false
  , className: Nothing
  }

-- | Output events
data Output
  = Rendered
  | LineSelected (Maybe SelectedLineRange)
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
  , dragSide :: Maybe SelectionSide
  , dragEndSide :: Maybe SelectionSide
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
  , dragSide: Nothing
  , dragEndSide: Nothing
  , dragMoved: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    ([ HP.ref (H.RefLabel "container")
    , HP.attr (HH.AttrName "data-component") "diff"
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
    renderDiff state.input
    -- Set up color scheme monitoring
    liftEffect setupColorSchemeMonitor

  Finalize -> do
    -- Cleanup diff renderer
    liftEffect cleanupDiff
    -- Cleanup color scheme monitor
    liftEffect cleanupColorSchemeMonitor

  Receive newInput -> do
    state <- H.get
    -- Check if files changed
    let filesChanged = 
          state.input.before /= newInput.before ||
          state.input.after /= newInput.after ||
          state.input.diffStyle /= newInput.diffStyle
    
    when filesChanged do
      H.modify_ _ { renderToken = state.renderToken + 1 }
      renderDiff newInput
    
    -- Update selected lines
    when (state.input.selectedLines /= newInput.selectedLines) do
      H.modify_ _ { lastSelection = newInput.selectedLines }
      liftEffect $ applyDiffSelection newInput.selectedLines (diffStyleToString newInput.diffStyle)
    
    -- Update commented lines
    when (state.input.commentedLines /= newInput.commentedLines) do
      liftEffect $ applyDiffCommentedLines newInput.commentedLines (diffStyleToString newInput.diffStyle)
    
    H.modify_ _ { input = newInput }

  HandleMouseDown me -> do
    state <- H.get
    when state.input.enableLineSelection do
      let button = ME.button me
      when (button == 0) do
        mLineInfo <- liftEffect $ diffLineFromMouseEvent me
        case mLineInfo of
          { line: Just line, numberColumn: false, side: mSide } -> do
            H.modify_ _ 
              { dragStart = Just line
              , dragEnd = Just line
              , dragSide = mSide
              , dragEndSide = mSide
              , dragMoved = false
              }
          _ -> pure unit

  HandleMouseMove me -> do
    state <- H.get
    when state.input.enableLineSelection do
      case state.dragStart of
        Nothing -> pure unit
        Just _ -> do
          let buttons = ME.buttons me
          if buttons == 0
            then H.modify_ _ 
              { dragStart = Nothing
              , dragEnd = Nothing
              , dragSide = Nothing
              , dragEndSide = Nothing
              , dragMoved = false
              }
            else do
              mLineInfo <- liftEffect $ diffLineFromMouseEvent me
              case mLineInfo.line of
                Nothing -> pure unit
                Just line -> do
                  H.modify_ _ 
                    { dragEnd = Just line
                    , dragEndSide = mLineInfo.side
                    , dragMoved = true
                    }
                  updateDragSelection
                  newState <- H.get
                  H.raise (LineSelected newState.lastSelection)

  HandleMouseUp -> do
    state <- H.get
    when state.input.enableLineSelection do
      case state.dragStart of
        Nothing -> pure unit
        Just startLine -> do
          if not state.dragMoved
            then do
              -- Single click - select single line
              let range = 
                    { start: startLine
                    , end: startLine
                    , side: state.dragSide
                    , endSide: Nothing
                    }
              H.modify_ _ { lastSelection = Just range }
              liftEffect $ applyDiffSelection (Just range) (diffStyleToString state.input.diffStyle)
              H.raise (LineSelectionEnd (Just range))
            else do
              updateDragSelection
              newState <- H.get
              H.raise (LineSelectionEnd newState.lastSelection)
          
          H.modify_ _ 
            { dragStart = Nothing
            , dragEnd = Nothing
            , dragSide = Nothing
            , dragEndSide = Nothing
            , dragMoved = false
            }

  HandleSelectionChange -> do
    state <- H.get
    when state.input.enableLineSelection do
      liftEffect updateDiffSelectionFromDOM

  RenderComplete -> do
    state <- H.get
    -- Apply selection after render
    liftEffect $ applyDiffSelection state.lastSelection (diffStyleToString state.input.diffStyle)
    -- Apply commented lines
    liftEffect $ applyDiffCommentedLines state.input.commentedLines (diffStyleToString state.input.diffStyle)
    -- Notify rendered
    H.raise Rendered

-- | Update drag selection
updateDragSelection :: forall m. MonadAff m => H.HalogenM State Action () Output m Unit
updateDragSelection = do
  state <- H.get
  case state.dragStart, state.dragEnd of
    Just start, Just end -> do
      let range = 
            { start
            , end
            , side: state.dragSide
            , endSide: if state.dragEndSide /= state.dragSide 
                       then state.dragEndSide 
                       else Nothing
            }
      H.modify_ _ { lastSelection = Just range }
      liftEffect $ applyDiffSelection (Just range) (diffStyleToString state.input.diffStyle)
    _, _ -> pure unit

-- | Render diff using FFI
renderDiff :: forall m. MonadAff m => Input -> H.HalogenM State Action () Output m Unit
renderDiff input = do
  mContainer <- H.getHTMLElementRef (H.RefLabel "container")
  for_ mContainer \container -> do
    liftEffect $ renderDiffFFI container input
    liftEffect $ scheduleDiffRenderComplete

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetSelectedLines range a -> do
    state <- H.get
    H.modify_ _ { lastSelection = range }
    liftEffect $ applyDiffSelection range (diffStyleToString state.input.diffStyle)
    pure (Just a)
  
  GetSelectedLines reply -> do
    state <- H.get
    pure (Just (reply state.lastSelection))
  
  Refresh a -> do
    state <- H.get
    renderDiff state.input
    pure (Just a)

-- ═══════════════════════════════════════════════════════════════════════════════
-- FFI (Minimal - only true DOM operations)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Style variables from pierre
foreign import styleVariables :: String

-- | Render diff using pierre/diffs FileDiff renderer
foreign import renderDiffFFI :: forall a. a -> Input -> Effect Unit

-- | Cleanup diff renderer
foreign import cleanupDiff :: Effect Unit

-- | Apply selection to rendered diff lines
foreign import applyDiffSelection :: Maybe SelectedLineRange -> String -> Effect Unit

-- | Apply commented lines styling to diff
foreign import applyDiffCommentedLines :: Array SelectedLineRange -> String -> Effect Unit

-- | Setup color scheme monitoring
foreign import setupColorSchemeMonitor :: Effect Unit

-- | Cleanup color scheme monitor
foreign import cleanupColorSchemeMonitor :: Effect Unit

-- | Schedule diff render complete
foreign import scheduleDiffRenderComplete :: Effect Unit

-- | Get line info from mouse event (with side awareness)
foreign import diffLineFromMouseEvent :: ME.MouseEvent -> Effect { line :: Maybe Int, numberColumn :: Boolean, side :: Maybe SelectionSide }

-- | Update selection from DOM selection API
foreign import updateDiffSelectionFromDOM :: Effect Unit
