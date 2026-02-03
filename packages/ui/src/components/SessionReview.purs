-- | Session Review Component
-- | Migrated from: forge-dev/packages/ui/src/components/session-review.tsx
-- | Original lines: 638
-- |
-- | Review session changes with inline diff viewer and commenting.
-- | Supports unified/split diff views and line-level comments.
-- |
-- | Data Attributes:
-- | - data-component="session-review": Root container
-- | - data-slot="session-review-header": Header section
-- | - data-slot="session-review-title": Title text
-- | - data-slot="session-review-actions": Action buttons
-- | - data-slot="session-review-container": Content container
-- | - data-slot="session-review-accordion-item": File accordion item
-- | - data-slot="session-review-trigger-content": Accordion trigger
-- | - data-slot="session-review-file-info": File info display
-- | - data-slot="session-review-file-name-container": File name area
-- | - data-slot="session-review-directory": Directory path
-- | - data-slot="session-review-filename": File name
-- | - data-slot="session-review-view-button": View file button
-- | - data-slot="session-review-trigger-actions": Trigger actions
-- | - data-slot="session-review-change": Change type indicator
-- | - data-slot="session-review-accordion-content": Accordion content
-- | - data-slot="session-review-diff-wrapper": Diff wrapper
-- | - data-file: File path attribute
-- | - data-selected: Selected state
-- | - data-type: Change type (added | removed | update)

module UI.Components.SessionReview
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , SessionReviewDiffStyle(..)
  , SessionReviewComment
  , SessionReviewLineComment
  , SessionReviewFocus
  , FileDiff
  , defaultInput
  ) where

import Prelude

import Data.Array (filter, length, map)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import UI.Components.Diff (SelectedLineRange, SelectionSide)

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Diff style
data SessionReviewDiffStyle
  = Unified
  | Split

derive instance eqSessionReviewDiffStyle :: Eq SessionReviewDiffStyle

diffStyleToString :: SessionReviewDiffStyle -> String
diffStyleToString Unified = "unified"
diffStyleToString Split = "split"

-- | Comment type
type SessionReviewComment =
  { id :: String
  , file :: String
  , selection :: SelectedLineRange
  , comment :: String
  }

-- | Line comment for creation
type SessionReviewLineComment =
  { file :: String
  , selection :: SelectedLineRange
  , comment :: String
  , preview :: Maybe String
  }

-- | Focus target
type SessionReviewFocus =
  { file :: String
  , id :: String
  }

-- | File diff type
type FileDiff =
  { file :: String
  , before :: Maybe String
  , after :: Maybe String
  , additions :: Int
  , deletions :: Int
  , preloaded :: Maybe PreloadedDiff
  }

type PreloadedDiff =
  { prerenderedHTML :: String
  }

-- | Component input props
type Input =
  { split :: Boolean
  , diffStyle :: SessionReviewDiffStyle
  , onDiffStyleChange :: Maybe (SessionReviewDiffStyle -> Effect Unit)
  , onDiffRendered :: Maybe (Effect Unit)
  , onLineComment :: Maybe (SessionReviewLineComment -> Effect Unit)
  , comments :: Array SessionReviewComment
  , focusedComment :: Maybe SessionReviewFocus
  , onFocusedCommentChange :: Maybe (Maybe SessionReviewFocus -> Effect Unit)
  , focusedFile :: Maybe String
  , open :: Maybe (Array String)
  , onOpenChange :: Maybe (Array String -> Effect Unit)
  , className :: Maybe String
  , classes :: Maybe SessionReviewClasses
  , diffs :: Array FileDiff
  , onViewFile :: Maybe (String -> Effect Unit)
  }

type SessionReviewClasses =
  { root :: Maybe String
  , header :: Maybe String
  , container :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { split: false
  , diffStyle: Unified
  , onDiffStyleChange: Nothing
  , onDiffRendered: Nothing
  , onLineComment: Nothing
  , comments: []
  , focusedComment: Nothing
  , onFocusedCommentChange: Nothing
  , focusedFile: Nothing
  , open: Nothing
  , onOpenChange: Nothing
  , className: Nothing
  , classes: Nothing
  , diffs: []
  , onViewFile: Nothing
  }

-- | Output events
data Output
  = DiffStyleChanged SessionReviewDiffStyle
  | DiffRendered
  | LineCommentCreated SessionReviewLineComment
  | OpenChanged (Array String)
  | FocusedCommentChanged (Maybe SessionReviewFocus)
  | ViewFileClicked String

-- | Queries
data Query a
  = SetOpen (Array String) a
  | GetOpen (Array String -> a)
  | FocusComment SessionReviewFocus a

-- | Internal state
type State =
  { input :: Input
  , storeOpen :: Array String
  , selection :: Maybe SelectionState
  , commenting :: Maybe SelectionState
  , opened :: Maybe SessionReviewFocus
  }

type SelectionState =
  { file :: String
  , range :: SelectedLineRange
  }

-- | Internal actions
data Action
  = Initialize
  | Finalize
  | Receive Input
  | HandleOpenChange (Array String)
  | HandleExpandCollapseAll
  | HandleDiffStyleChange SessionReviewDiffStyle
  | HandleViewFile String
  | HandleLineSelected String (Maybe SelectedLineRange)
  | HandleLineSelectionEnd String (Maybe SelectedLineRange)
  | HandleCommentClick SessionReviewComment
  | HandleDraftSubmit String SelectedLineRange String
  | HandleDraftCancel

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
  let defaultOpen = if length input.diffs > 10 then [] else map _.file input.diffs
  in { input
     , storeOpen: fromMaybe defaultOpen input.open
     , selection: Nothing
     , commenting: Nothing
     , opened: Nothing
     }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    ([ HP.ref (H.RefLabel "scroll")
    , HP.attr (HH.AttrName "data-component") "session-review"
    ] <> classAttrs state)
    [ renderHeader state
    , renderContainer state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.div
    ([ HP.attr (HH.AttrName "data-slot") "session-review-header" 
    ] <> headerClassAttr state)
    [ HH.div
        [ HP.attr (HH.AttrName "data-slot") "session-review-title" ]
        [ HH.text "Changes" ]
    , HH.div
        [ HP.attr (HH.AttrName "data-slot") "session-review-actions" ]
        [ renderDiffStyleToggle state
        , renderExpandCollapseButton state
        ]
    ]

renderDiffStyleToggle :: forall m. State -> H.ComponentHTML Action () m
renderDiffStyleToggle state =
  case state.input.onDiffStyleChange of
    Nothing -> HH.text ""
    Just _ ->
      HH.div
        [ HP.attr (HH.AttrName "data-component") "radio-group" ]
        [ HH.button
            [ HP.type_ HP.ButtonButton
            , HP.attr (HH.AttrName "data-selected") (if state.input.diffStyle == Unified then "true" else "false")
            , HE.onClick \_ -> HandleDiffStyleChange Unified
            ]
            [ HH.text "Unified" ]
        , HH.button
            [ HP.type_ HP.ButtonButton
            , HP.attr (HH.AttrName "data-selected") (if state.input.diffStyle == Split then "true" else "false")
            , HE.onClick \_ -> HandleDiffStyleChange Split
            ]
            [ HH.text "Split" ]
        ]

renderExpandCollapseButton :: forall m. State -> H.ComponentHTML Action () m
renderExpandCollapseButton state =
  let currentOpen = fromMaybe state.storeOpen state.input.open
      isExpanded = length currentOpen > 0
  in HH.button
       [ HP.type_ HP.ButtonButton
       , HE.onClick \_ -> HandleExpandCollapseAll
       ]
       [ HH.text (if isExpanded then "Collapse All" else "Expand All") ]

renderContainer :: forall m. State -> H.ComponentHTML Action () m
renderContainer state =
  HH.div
    ([ HP.attr (HH.AttrName "data-slot") "session-review-container"
    ] <> containerClassAttr state)
    [ renderDiffAccordion state ]

renderDiffAccordion :: forall m. State -> H.ComponentHTML Action () m
renderDiffAccordion state =
  HH.div
    [ HP.attr (HH.AttrName "data-component") "accordion" ]
    (map (renderDiffItem state) state.input.diffs)

renderDiffItem :: forall m. State -> FileDiff -> H.ComponentHTML Action () m
renderDiffItem state diff =
  let beforeText = fromMaybe "" diff.before
      afterText = fromMaybe "" diff.after
      isAdded = beforeText == "" && afterText /= ""
      isDeleted = afterText == "" && beforeText /= ""
      changeType = if isAdded then "added"
                   else if isDeleted then "removed"
                   else "update"
  in HH.div
       [ HP.attr (HH.AttrName "data-slot") "session-review-accordion-item"
       , HP.attr (HH.AttrName "data-file") diff.file
       , HP.attr (HH.AttrName "data-type") changeType
       ]
       [ renderDiffTrigger state diff changeType
       , renderDiffContent state diff
       ]

renderDiffTrigger :: forall m. State -> FileDiff -> String -> H.ComponentHTML Action () m
renderDiffTrigger state diff changeType =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "session-review-trigger-content" ]
    [ HH.div
        [ HP.attr (HH.AttrName "data-slot") "session-review-file-info" ]
        [ HH.div
            [ HP.attr (HH.AttrName "data-slot") "session-review-file-name-container" ]
            [ renderDirectory diff.file
            , HH.span
                [ HP.attr (HH.AttrName "data-slot") "session-review-filename" ]
                [ HH.text (getFilename diff.file) ]
            , renderViewButton state diff.file
            ]
        ]
    , HH.div
        [ HP.attr (HH.AttrName "data-slot") "session-review-trigger-actions" ]
        [ renderChangeType changeType
        , renderDiffChanges diff
        ]
    ]

renderDirectory :: forall m. String -> H.ComponentHTML Action () m
renderDirectory file =
  if not (containsSlash file)
    then HH.text ""
    else HH.span
      [ HP.attr (HH.AttrName "data-slot") "session-review-directory" ]
      [ HH.text (getDirectory file) ]

renderViewButton :: forall m. State -> String -> H.ComponentHTML Action () m
renderViewButton state file =
  case state.input.onViewFile of
    Nothing -> HH.text ""
    Just _ ->
      HH.button
        [ HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "data-slot") "session-review-view-button"
        , HE.onClick \_ -> HandleViewFile file
        ]
        [ HH.text "View" ]

renderChangeType :: forall m. String -> H.ComponentHTML Action () m
renderChangeType changeType =
  HH.span
    [ HP.attr (HH.AttrName "data-slot") "session-review-change"
    , HP.attr (HH.AttrName "data-type") changeType
    ]
    [ HH.text (case changeType of
        "added" -> "Added"
        "removed" -> "Removed"
        _ -> "Modified")
    ]

renderDiffChanges :: forall m. FileDiff -> H.ComponentHTML Action () m
renderDiffChanges diff =
  HH.span []
    [ HH.text ("+" <> show diff.additions <> " -" <> show diff.deletions) ]

renderDiffContent :: forall m. State -> FileDiff -> H.ComponentHTML Action () m
renderDiffContent state diff =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "session-review-accordion-content" ]
    [ HH.div
        [ HP.attr (HH.AttrName "data-slot") "session-review-diff-wrapper" ]
        [ HH.text "Diff component would render here" ]
    ]

-- Helpers
classAttrs :: forall r i. State -> Array (HP.IProp r i)
classAttrs state =
  let mClass = state.input.className
      mRoot = state.input.classes >>= _.root
  in case mClass, mRoot of
    Just c, Just r -> [ HP.class_ (HH.ClassName (c <> " " <> r)) ]
    Just c, Nothing -> [ HP.class_ (HH.ClassName c) ]
    Nothing, Just r -> [ HP.class_ (HH.ClassName r) ]
    Nothing, Nothing -> []

headerClassAttr :: forall r i. State -> Array (HP.IProp r i)
headerClassAttr state =
  case state.input.classes >>= _.header of
    Nothing -> []
    Just cls -> [ HP.class_ (HH.ClassName cls) ]

containerClassAttr :: forall r i. State -> Array (HP.IProp r i)
containerClassAttr state =
  case state.input.classes >>= _.container of
    Nothing -> []
    Just cls -> [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Finalize -> pure unit

  Receive newInput -> 
    H.modify_ _ { input = newInput }

  HandleOpenChange newOpen -> do
    state <- H.get
    for_ state.input.onOpenChange \callback ->
      liftEffect $ callback newOpen
    when (state.input.open == Nothing) do
      H.modify_ _ { storeOpen = newOpen }
    H.raise (OpenChanged newOpen)

  HandleExpandCollapseAll -> do
    state <- H.get
    let currentOpen = fromMaybe state.storeOpen state.input.open
        next = if length currentOpen > 0 then [] else map _.file state.input.diffs
    handleAction (HandleOpenChange next)

  HandleDiffStyleChange style -> do
    state <- H.get
    for_ state.input.onDiffStyleChange \callback ->
      liftEffect $ callback style
    H.raise (DiffStyleChanged style)

  HandleViewFile file -> do
    state <- H.get
    for_ state.input.onViewFile \callback ->
      liftEffect $ callback file
    H.raise (ViewFileClicked file)

  HandleLineSelected file range -> do
    case range of
      Nothing -> H.modify_ _ { selection = Nothing }
      Just r -> H.modify_ _ { selection = Just { file, range: r } }

  HandleLineSelectionEnd file range -> do
    case range of
      Nothing -> H.modify_ _ { commenting = Nothing }
      Just r -> do
        H.modify_ _ 
          { selection = Just { file, range: r }
          , commenting = Just { file, range: r }
          }

  HandleCommentClick comment -> do
    state <- H.get
    let focus = { file: comment.file, id: comment.id }
    H.modify_ _ 
      { opened = Just focus
      , selection = Just { file: comment.file, range: comment.selection }
      }

  HandleDraftSubmit file range comment -> do
    state <- H.get
    let lineComment = 
          { file
          , selection: range
          , comment
          , preview: Nothing
          }
    for_ state.input.onLineComment \callback ->
      liftEffect $ callback lineComment
    H.modify_ _ { commenting = Nothing }
    H.raise (LineCommentCreated lineComment)

  HandleDraftCancel ->
    H.modify_ _ { commenting = Nothing }

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetOpen newOpen a -> do
    handleAction (HandleOpenChange newOpen)
    pure (Just a)

  GetOpen reply -> do
    state <- H.get
    let current = fromMaybe state.storeOpen state.input.open
    pure (Just (reply current))

  FocusComment focus a -> do
    H.modify_ _ { opened = Just focus }
    pure (Just a)

-- ═══════════════════════════════════════════════════════════════════════════════
-- FFI
-- ═══════════════════════════════════════════════════════════════════════════════

foreign import getDirectory :: String -> String
foreign import getFilename :: String -> String
foreign import containsSlash :: String -> Boolean
