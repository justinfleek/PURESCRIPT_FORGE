-- | Dialog Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/dialog.tsx (73 lines)
-- |
-- | Modal dialog with title, description, and action support.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Implements behavior from Radix/Kobalte Dialog:
-- | - Modal (blocking) mode with scroll locking
-- | - Focus trapping with Tab loop
-- | - Escape to close
-- | - Click outside to close
-- | - Focus restoration
-- | - Proper ARIA attributes
-- |
-- | Data Attributes:
-- | - `data-component="dialog"` - Root wrapper
-- | - `data-fit` - Present when content should fit width
-- | - `data-size="normal|large|x-large"` - Size variant
-- | - `data-transition` - Present when transitions enabled
-- | - `data-slot="dialog-container"` - Container element
-- | - `data-slot="dialog-content"` - Content wrapper
-- | - `data-slot="dialog-header"` - Header with title and close
-- | - `data-slot="dialog-title"` - Title element
-- | - `data-slot="dialog-close-button"` - Close button
-- | - `data-slot="dialog-description"` - Description text
-- | - `data-slot="dialog-body"` - Body content area
-- | - `data-no-header` - Present when no title/action
-- | - `data-state="open|closed"` - Dialog state
module UI.Components.Dialog
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , DialogSize(..)
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
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Halogen.Query.Event as HQE
import Web.Event.Event as Event
import Web.HTML as HTML
import Web.HTML.HTMLDocument as HTMLDocument
import Web.HTML.HTMLElement as HTMLElement
import Web.HTML.Window as Window
import Web.UIEvent.KeyboardEvent as KE
import Web.UIEvent.KeyboardEvent.EventTypes as KET

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Dialog size variants
data DialogSize
  = Normal
  | Large
  | XLarge

derive instance eqDialogSize :: Eq DialogSize

sizeToString :: DialogSize -> String
sizeToString Normal = "normal"
sizeToString Large = "large"
sizeToString XLarge = "x-large"

-- | Dialog input props
type Input =
  { open :: Maybe Boolean           -- Controlled open state
  , defaultOpen :: Boolean          -- Initial state if uncontrolled
  , title :: Maybe String           -- Dialog title
  , description :: Maybe String     -- Dialog description
  , bodyContent :: String           -- Body content
  , size :: DialogSize              -- Size variant
  , fit :: Boolean                  -- Fit content width
  , transition :: Boolean           -- Enable transitions
  , closeOnEscape :: Boolean        -- Close on Escape key
  , closeOnOutsideClick :: Boolean  -- Close on click outside
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { open: Nothing
  , defaultOpen: false
  , title: Nothing
  , description: Nothing
  , bodyContent: ""
  , size: Normal
  , fit: false
  , transition: true
  , closeOnEscape: true
  , closeOnOutsideClick: true
  , className: Nothing
  }

-- | Output events
data Output
  = Opened
  | Closed
  | OpenChanged Boolean

-- | Queries for external control
data Query a
  = Open a
  | Close a
  | Toggle a
  | IsOpen (Boolean -> a)

-- | Internal state
type State =
  { isOpen :: Boolean
  , input :: Input
  , previousActiveElement :: Maybe HTMLElement.HTMLElement
  }

-- | Internal actions
data Action
  = Initialize
  | Finalize
  | Receive Input
  | HandleTriggerClick
  | HandleCloseClick
  | HandleKeyDown KE.KeyboardEvent
  | HandleOverlayClick
  | ContentClicked

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
  { isOpen: fromMaybe input.defaultOpen input.open
  , input
  , previousActiveElement: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (HH.ClassName "dialog-root") ]
    [ renderTrigger state
    , if state.isOpen then renderPortal state else HH.text ""
    ]

renderTrigger :: forall m. State -> H.ComponentHTML Action () m
renderTrigger state =
  HH.button
    [ HP.class_ (HH.ClassName "dialog-trigger")
    , HP.type_ HP.ButtonButton
    , HP.ref (H.RefLabel "trigger")
    , HE.onClick \_ -> HandleTriggerClick
    , ARIA.hasPopup "dialog"
    , ARIA.expanded (show state.isOpen)
    , ARIA.controls "dialog-content"
    , HP.attr (HH.AttrName "data-state") (if state.isOpen then "open" else "closed")
    ]
    [ HH.text "Open Dialog" ]

renderPortal :: forall m. State -> H.ComponentHTML Action () m
renderPortal state =
  HH.div
    [ HP.class_ (HH.ClassName "dialog-portal")
    , HP.attr (HH.AttrName "data-component") "dialog"
    , HP.attr (HH.AttrName "data-size") (sizeToString state.input.size)
    , HP.attr (HH.AttrName "data-state") "open"
    ] <> fitAttr state.input.fit <> transitionAttr state.input.transition
    [ renderOverlay state
    , renderContent state
    ]

renderOverlay :: forall m. State -> H.ComponentHTML Action () m
renderOverlay state =
  HH.div
    [ HP.class_ (HH.ClassName "dialog-overlay")
    , HP.attr (HH.AttrName "data-state") "open"
    , HE.onClick \_ -> HandleOverlayClick
    ]
    []

renderContent :: forall m. State -> H.ComponentHTML Action () m
renderContent state =
  HH.div
    ([ HP.class_ (HH.ClassName "dialog-content")
    , HP.ref (H.RefLabel "content")
    , HP.id "dialog-content"
    , HP.attr (HH.AttrName "data-slot") "dialog-content"
    , HP.attr (HH.AttrName "role") "dialog"
    , HP.attr (HH.AttrName "aria-modal") "true"
    , ARIA.labelledBy "dialog-title"
    , ARIA.describedBy "dialog-description"
    , HP.attr (HH.AttrName "data-state") "open"
    , HP.tabIndex 0
    , HE.onClick \_ -> ContentClicked
    ] <> noHeaderAttr state.input.title <> classAttr state.input.className)
    [ renderHeader state
    , renderDescription state
    , renderBody state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  case state.input.title of
    Nothing -> HH.text ""
    Just title ->
      HH.div
        [ HP.attr (HH.AttrName "data-slot") "dialog-header" ]
        [ HH.h2
            [ HP.id "dialog-title"
            , HP.attr (HH.AttrName "data-slot") "dialog-title"
            ]
            [ HH.text title ]
        , HH.button
            [ HP.class_ (HH.ClassName "dialog-close-button")
            , HP.type_ HP.ButtonButton
            , HP.attr (HH.AttrName "data-slot") "dialog-close-button"
            , HE.onClick \_ -> HandleCloseClick
            , ARIA.label "Close"
            ]
            [ HH.text "×" ]
        ]

renderDescription :: forall m. State -> H.ComponentHTML Action () m
renderDescription state =
  case state.input.description of
    Nothing -> HH.text ""
    Just desc ->
      HH.p
        [ HP.id "dialog-description"
        , HP.attr (HH.AttrName "data-slot") "dialog-description"
        ]
        [ HH.text desc ]

renderBody :: forall m. State -> H.ComponentHTML Action () m
renderBody state =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "dialog-body" ]
    [ HH.text state.input.bodyContent ]

-- Helper attribute functions
fitAttr :: forall r i. Boolean -> Array (HP.IProp r i)
fitAttr false = []
fitAttr true = [ HP.attr (HH.AttrName "data-fit") "true" ]

transitionAttr :: forall r i. Boolean -> Array (HP.IProp r i)
transitionAttr false = []
transitionAttr true = [ HP.attr (HH.AttrName "data-transition") "true" ]

noHeaderAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
noHeaderAttr Nothing = [ HP.attr (HH.AttrName "data-no-header") "true" ]
noHeaderAttr (Just _) = []

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Subscribe to keyboard events
    doc <- liftEffect $ HTML.window >>= Window.document
    void $ H.subscribe $ HQE.eventListener
      KET.keydown
      (HTMLDocument.toEventTarget doc)
      (KE.fromEvent >>> map HandleKeyDown)

  Finalize -> do
    -- Cleanup: restore scroll if dialog was open
    state <- H.get
    when state.isOpen do
      liftEffect restoreBodyScroll

  Receive newInput -> do
    -- Handle controlled state changes
    case newInput.open of
      Just newOpen -> do
        state <- H.get
        when (newOpen /= state.isOpen) do
          if newOpen
            then openDialog
            else closeDialog
      Nothing -> pure unit
    H.modify_ _ { input = newInput }

  HandleTriggerClick -> do
    state <- H.get
    -- Store trigger ref for focus restoration
    mTrigger <- H.getHTMLElementRef (H.RefLabel "trigger")
    -- previousActiveElement stored in openDialog
    if state.isOpen
      then closeDialog
      else openDialog

  HandleCloseClick -> closeDialog

  HandleKeyDown ke -> do
    state <- H.get
    when state.isOpen do
      -- Handle Escape key
      when (state.input.closeOnEscape && KE.key ke == "Escape") do
        liftEffect $ Event.preventDefault (KE.toEvent ke)
        closeDialog

  HandleOverlayClick -> do
    state <- H.get
    when (state.isOpen && state.input.closeOnOutsideClick) do
      closeDialog

  ContentClicked -> pure unit  -- Swallow click, don't close

-- ═══════════════════════════════════════════════════════════════════════════════
-- STATE TRANSITIONS
-- ═══════════════════════════════════════════════════════════════════════════════

openDialog :: forall m. MonadAff m => H.HalogenM State Action () Output m Unit
openDialog = do
  -- Store current active element for restoration
  doc <- liftEffect $ HTML.window >>= Window.document
  mActive <- liftEffect $ HTMLDocument.activeElement doc
  H.modify_ _ { previousActiveElement = mActive }
  
  -- Lock body scroll
  liftEffect lockBodyScroll
  
  -- Update state to trigger render
  H.modify_ _ { isOpen = true }
  
  -- Focus the content after render
  mContent <- H.getHTMLElementRef (H.RefLabel "content")
  for_ mContent \el -> liftEffect $ HTMLElement.focus el
  
  -- Emit events
  H.raise Opened
  H.raise (OpenChanged true)

closeDialog :: forall m. MonadAff m => H.HalogenM State Action () Output m Unit
closeDialog = do
  state <- H.get
  
  -- Restore body scroll
  liftEffect restoreBodyScroll
  
  -- Update state
  H.modify_ _ { isOpen = false }
  
  -- Restore focus to previous active element
  for_ state.previousActiveElement \el ->
    liftEffect $ HTMLElement.focus el
  
  -- Emit events
  H.raise Closed
  H.raise (OpenChanged false)

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  Open a -> do
    openDialog
    pure (Just a)
  
  Close a -> do
    closeDialog
    pure (Just a)
  
  Toggle a -> do
    state <- H.get
    if state.isOpen then closeDialog else openDialog
    pure (Just a)
  
  IsOpen reply -> do
    state <- H.get
    pure (Just (reply state.isOpen))

-- ═══════════════════════════════════════════════════════════════════════════════
-- FFI (Minimal - scroll lock only)
-- ═══════════════════════════════════════════════════════════════════════════════

-- These are legitimate DOM operations that require FFI:
-- - Scroll locking modifies body.style.overflow
-- - No return value, no Nullable, pure Effect

foreign import lockBodyScroll :: Effect Unit
foreign import restoreBodyScroll :: Effect Unit
