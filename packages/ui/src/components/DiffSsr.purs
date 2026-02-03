-- | Diff SSR Component
-- | Migrated from: forge-dev/packages/ui/src/components/diff-ssr.tsx
-- | Original lines: 288
-- |
-- | Server-side rendered diff component with hydration support.
-- | Uses preloaded diff results for faster initial render.
-- |
-- | Data Attributes:
-- | - data-component="diff": Root element
-- | - data-line: Line number
-- | - data-alt-line: Alternative line number
-- | - data-line-type: Line change type
-- | - data-code: Code block
-- | - data-deletions: Deletion side marker
-- | - data-diffs: Diffs container
-- | - data-comment-selected: Selected for comment
-- | - data-color-scheme: Theme color scheme
-- | - id="ssr-diff": SSR diff container

module UI.Components.DiffSsr
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , PreloadedDiff
  , defaultInput
  ) where

import Prelude

import Data.Foldable (for_)
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import UI.Components.Diff (SelectionSide(..), SelectedLineRange, FileInfo, DiffStyle(..))

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Preloaded diff result from server
type PreloadedDiff =
  { prerenderedHTML :: String
  }

-- | Line annotation type
type LineAnnotation =
  { lineNumber :: Int
  , side :: Maybe SelectionSide
  }

-- | SSR Diff component input props
type Input =
  { before :: Maybe FileInfo
  , after :: Maybe FileInfo
  , diffStyle :: DiffStyle
  , annotations :: Array LineAnnotation
  , selectedLines :: Maybe SelectedLineRange
  , commentedLines :: Array SelectedLineRange
  , preloadedDiff :: PreloadedDiff
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
  , preloadedDiff: { prerenderedHTML: "" }
  , className: Nothing
  }

-- | Output events
data Output
  = Rendered
  | Hydrated

-- | Queries for external control
data Query a
  = SetSelectedLines (Maybe SelectedLineRange) a
  | GetSelectedLines (Maybe SelectedLineRange -> a)
  | SetAnnotations (Array LineAnnotation) a

-- | Internal state
type State =
  { input :: Input
  , hydrated :: Boolean
  , lastSelection :: Maybe SelectedLineRange
  }

-- | Internal actions
data Action
  = Initialize
  | Finalize
  | Receive Input
  | HydrationComplete

-- | Slot type for parent components
type Slot id = H.Slot Query Output id

-- ══════��════════════════════════════════════════════════════════════════════════
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
  , hydrated: false
  , lastSelection: input.selectedLines
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
    ] <> classAttr state.input.className)
    [ renderDiffsTag state ]

renderDiffsTag :: forall m. State -> H.ComponentHTML Action () m
renderDiffsTag state =
  -- The diffs-container custom element with SSR content
  HH.element (HH.ElemName diffsTagName)
    [ HP.ref (H.RefLabel "diffsContainer")
    , HP.id "ssr-diff"
    ]
    [ renderSSRTemplate state ]

renderSSRTemplate :: forall m. State -> H.ComponentHTML Action () m
renderSSRTemplate state =
  -- Only render template on server, client will hydrate
  if isServer
    then HH.element (HH.ElemName "template")
           [ HP.attr (HH.AttrName "shadowrootmode") "open" ]
           [ HH.Raw state.input.preloadedDiff.prerenderedHTML ]
    else HH.text ""

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
    -- Only hydrate on client
    when (not isServer) do
      -- Set up color scheme
      liftEffect applyScheme
      -- Set up color scheme monitoring
      liftEffect setupColorSchemeMonitor
      -- Hydrate the SSR content
      hydrateDiff state.input
    H.raise Rendered

  Finalize -> do
    -- Cleanup
    liftEffect cleanupDiffSsr
    liftEffect cleanupColorSchemeMonitor

  Receive newInput -> do
    state <- H.get
    -- Update selected lines
    when (state.input.selectedLines /= newInput.selectedLines) do
      H.modify_ _ { lastSelection = newInput.selectedLines }
      liftEffect $ setSelectedLinesSsr newInput.selectedLines
    
    -- Update annotations
    when (state.input.annotations /= newInput.annotations) do
      liftEffect $ setAnnotationsSsr newInput.annotations
    
    -- Update commented lines
    when (state.input.commentedLines /= newInput.commentedLines) do
      liftEffect $ applyCommentedLinesSsr newInput.commentedLines (diffStyleToString newInput.diffStyle)
    
    H.modify_ _ { input = newInput }

  HydrationComplete -> do
    state <- H.get
    H.modify_ _ { hydrated = true }
    -- Apply initial selection
    liftEffect $ setSelectedLinesSsr state.lastSelection
    -- Apply commented lines
    liftEffect $ applyCommentedLinesSsr state.input.commentedLines (diffStyleToString state.input.diffStyle)
    H.raise Hydrated

-- | Hydrate diff using FFI
hydrateDiff :: forall m. MonadAff m => Input -> H.HalogenM State Action () Output m Unit
hydrateDiff input = do
  mContainer <- H.getHTMLElementRef (H.RefLabel "container")
  mDiffsContainer <- H.getHTMLElementRef (H.RefLabel "diffsContainer")
  for_ mContainer \container ->
    for_ mDiffsContainer \diffsContainer -> do
      liftEffect $ hydrateDiffFFI container diffsContainer input

diffStyleToString :: DiffStyle -> String
diffStyleToString Unified = "unified"
diffStyleToString Split = "split"

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetSelectedLines range a -> do
    H.modify_ _ { lastSelection = range }
    liftEffect $ setSelectedLinesSsr range
    pure (Just a)
  
  GetSelectedLines reply -> do
    state <- H.get
    pure (Just (reply state.lastSelection))
  
  SetAnnotations annotations a -> do
    liftEffect $ setAnnotationsSsr annotations
    pure (Just a)

-- ═══════════════════════════════════════════════════════════════════════════════
-- FFI (Minimal - only true DOM operations)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Style variables from pierre
foreign import styleVariables :: String

-- | DIFFS_TAG_NAME constant
foreign import diffsTagName :: String

-- | Check if running on server
foreign import isServer :: Boolean

-- | Apply color scheme
foreign import applyScheme :: Effect Unit

-- | Setup color scheme monitoring
foreign import setupColorSchemeMonitor :: Effect Unit

-- | Cleanup color scheme monitor
foreign import cleanupColorSchemeMonitor :: Effect Unit

-- | Hydrate SSR diff content
foreign import hydrateDiffFFI :: forall a b. a -> b -> Input -> Effect Unit

-- | Cleanup SSR diff
foreign import cleanupDiffSsr :: Effect Unit

-- | Set selected lines on SSR diff
foreign import setSelectedLinesSsr :: Maybe SelectedLineRange -> Effect Unit

-- | Set annotations on SSR diff
foreign import setAnnotationsSsr :: Array { lineNumber :: Int, side :: Maybe SelectionSide } -> Effect Unit

-- | Apply commented lines styling to SSR diff
foreign import applyCommentedLinesSsr :: Array SelectedLineRange -> String -> Effect Unit
