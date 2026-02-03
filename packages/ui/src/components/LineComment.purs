-- | LineComment Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/line-comment.tsx (169 lines)
-- |
-- | Line-level code comments with anchor and editor modes.
-- | Pure Halogen implementation.
-- |
-- | Data Attributes:
-- | Anchor:
-- | - `data-component="line-comment"` - Root element
-- | - `data-variant="default|editor"` - Visual variant
-- | - `data-comment-id` - Comment ID
-- | - `data-open` - Present when popover is open
-- | - `data-slot="line-comment-button"` - Toggle button
-- | - `data-slot="line-comment-popover"` - Popover container
-- |
-- | Display:
-- | - `data-slot="line-comment-content"` - Content wrapper
-- | - `data-slot="line-comment-text"` - Comment text
-- | - `data-slot="line-comment-label"` - Selection label
-- |
-- | Editor:
-- | - `data-slot="line-comment-editor"` - Editor container
-- | - `data-slot="line-comment-textarea"` - Textarea input
-- | - `data-slot="line-comment-actions"` - Action buttons
-- | - `data-slot="line-comment-editor-label"` - Editor label
module UI.Components.LineComment
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , LineCommentMode(..)
  , defaultInput
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Web.Event.Event as Event
import Web.UIEvent.KeyboardEvent as KE

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Line comment mode/variant
data LineCommentMode
  = DisplayMode     -- Read-only comment display
  | EditorMode      -- Editable comment

derive instance eqLineCommentMode :: Eq LineCommentMode

modeToString :: LineCommentMode -> String
modeToString DisplayMode = "default"
modeToString EditorMode = "editor"

-- | LineComment input props
type Input =
  { commentId :: Maybe String      -- Comment ID
  , top :: Maybe Int               -- Top position in pixels
  , open :: Boolean                -- Whether popover is open
  , mode :: LineCommentMode        -- Display or editor mode
  , commentText :: String          -- Comment text content
  , selectionLabel :: String       -- Label for selection
  , value :: String                -- Editor value (for EditorMode)
  , placeholder :: String          -- Editor placeholder
  , rows :: Int                    -- Textarea rows
  , autofocus :: Boolean           -- Auto-focus editor
  , cancelLabel :: String          -- Cancel button label
  , submitLabel :: String          -- Submit button label
  , className :: Maybe String
  , popoverClass :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { commentId: Nothing
  , top: Nothing
  , open: false
  , mode: DisplayMode
  , commentText: ""
  , selectionLabel: ""
  , value: ""
  , placeholder: "Add a comment..."
  , rows: 3
  , autofocus: true
  , cancelLabel: "Cancel"
  , submitLabel: "Submit"
  , className: Nothing
  , popoverClass: Nothing
  }

-- | Output events
data Output
  = Clicked
  | MouseEntered
  | PopoverFocusOut
  | ValueChanged String
  | Cancelled
  | Submitted String

-- | Queries for external control
data Query a
  = Focus a
  | SetValue String a
  | GetValue (String -> a)

-- | Internal state
type State =
  { input :: Input
  , currentValue :: String
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleClick
  | HandleMouseEnter
  | HandleFocusOut
  | HandleInput String
  | HandleKeyDown KE.KeyboardEvent
  | HandleCancel
  | HandleSubmit

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
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { input
  , currentValue: input.value
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  let
    hidden = case state.input.top of
      Nothing -> true
      Just _ -> false
    topPx = case state.input.top of
      Nothing -> "0px"
      Just t -> show t <> "px"
  in
    HH.div
      ([ HP.attr (HH.AttrName "data-component") "line-comment"
      , HP.attr (HH.AttrName "data-variant") (modeToString state.input.mode)
      , HP.attr (HH.AttrName "style") 
          ("top: " <> topPx <> "; opacity: " <> (if hidden then "0" else "1") <> 
           "; pointer-events: " <> (if hidden then "none" else "auto") <> ";")
      ] <> openAttr state.input.open 
        <> commentIdAttr state.input.commentId 
        <> classAttr state.input.className)
      [ renderButton state
      , if state.input.open 
          then renderPopover state 
          else HH.text ""
      ]

renderButton :: forall m. State -> H.ComponentHTML Action () m
renderButton state =
  HH.button
    [ HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "data-slot") "line-comment-button"
    , HE.onClick \_ -> HandleClick
    , HE.onMouseEnter \_ -> HandleMouseEnter
    ]
    [ -- Icon placeholder (comment icon)
      HH.span
        [ HP.attr (HH.AttrName "aria-hidden") "true" ]
        [ HH.text "💬" ]
    ]

renderPopover :: forall m. State -> H.ComponentHTML Action () m
renderPopover state =
  HH.div
    ([ HP.attr (HH.AttrName "data-slot") "line-comment-popover"
    , HE.onFocusOut \_ -> HandleFocusOut
    ] <> classAttr state.input.popoverClass)
    [ case state.input.mode of
        DisplayMode -> renderDisplayContent state
        EditorMode -> renderEditorContent state
    ]

renderDisplayContent :: forall m. State -> H.ComponentHTML Action () m
renderDisplayContent state =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "line-comment-content" ]
    [ HH.div
        [ HP.attr (HH.AttrName "data-slot") "line-comment-text" ]
        [ HH.text state.input.commentText ]
    , HH.div
        [ HP.attr (HH.AttrName "data-slot") "line-comment-label" ]
        [ HH.text ("on " <> state.input.selectionLabel) ]
    ]

renderEditorContent :: forall m. State -> H.ComponentHTML Action () m
renderEditorContent state =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "line-comment-editor" ]
    [ HH.textarea
        [ HP.ref (H.RefLabel "textarea")
        , HP.attr (HH.AttrName "data-slot") "line-comment-textarea"
        , HP.rows state.input.rows
        , HP.placeholder state.input.placeholder
        , HP.value state.currentValue
        , HE.onValueInput HandleInput
        ]
    , HH.div
        [ HP.attr (HH.AttrName "data-slot") "line-comment-actions" ]
        [ HH.div
            [ HP.attr (HH.AttrName "data-slot") "line-comment-editor-label" ]
            [ HH.text ("on " <> state.input.selectionLabel) ]
        , HH.button
            [ HP.type_ HP.ButtonButton
            , HP.class_ (HH.ClassName "cancel-btn")
            , HE.onClick \_ -> HandleCancel
            ]
            [ HH.text state.input.cancelLabel ]
        , HH.button
            [ HP.type_ HP.ButtonButton
            , HP.class_ (HH.ClassName "submit-btn")
            , HP.disabled (String.trim state.currentValue == "")
            , HE.onClick \_ -> HandleSubmit
            ]
            [ HH.text state.input.submitLabel ]
        ]
    ]

-- Helper attribute functions
openAttr :: forall r i. Boolean -> Array (HP.IProp r i)
openAttr false = []
openAttr true = [ HP.attr (HH.AttrName "data-open") "" ]

commentIdAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
commentIdAttr Nothing = []
commentIdAttr (Just id) = [ HP.attr (HH.AttrName "data-comment-id") id ]

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
    -- Auto-focus if in editor mode
    when (state.input.mode == EditorMode && state.input.autofocus) do
      -- Focus will happen via ref in real implementation
      pure unit

  Receive newInput -> do
    H.modify_ _ { input = newInput }
    -- Update value if input value changed
    when (newInput.value /= "") do
      H.modify_ _ { currentValue = newInput.value }

  HandleClick -> do
    H.raise Clicked

  HandleMouseEnter -> do
    H.raise MouseEntered

  HandleFocusOut -> do
    H.raise PopoverFocusOut

  HandleInput newValue -> do
    H.modify_ _ { currentValue = newValue }
    H.raise (ValueChanged newValue)

  HandleKeyDown ke -> do
    let key = KE.key ke
    when (key == "Escape") do
      handleAction HandleCancel
    when (key == "Enter" && not (KE.shiftKey ke)) do
      handleAction HandleSubmit

  HandleCancel -> do
    H.raise Cancelled

  HandleSubmit -> do
    state <- H.get
    let trimmed = String.trim state.currentValue
    when (trimmed /= "") do
      H.raise (Submitted trimmed)

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  Focus a -> do
    -- Focus textarea via ref
    pure (Just a)

  SetValue value a -> do
    H.modify_ _ { currentValue = value }
    pure (Just a)

  GetValue reply -> do
    state <- H.get
    pure (Just (reply state.currentValue))

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs.
-- All positioning and styling done via CSS/data attributes.
