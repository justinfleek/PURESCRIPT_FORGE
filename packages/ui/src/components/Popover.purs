-- | Popover Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/popover.tsx (167 lines)
-- |
-- | Floating content panel with trigger element.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-slot="popover-trigger"` - Trigger element
-- | - `data-component="popover-content"` - Content container
-- | - `data-slot="popover-header"` - Header with title and close
-- | - `data-slot="popover-title"` - Title element
-- | - `data-slot="popover-close-button"` - Close button
-- | - `data-slot="popover-description"` - Description text
-- | - `data-slot="popover-body"` - Body content area
-- | - `data-open="true|false"` - Open state
module UI.Components.Popover
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , defaultInput
  ) where

import Prelude

import Data.Const (Const)
import Data.Maybe (Maybe(..))
import Data.Void (Void)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Type.Proxy (Proxy(..))
import Web.HTML.HTMLElement as HTMLElement
import Web.UIEvent.KeyboardEvent as KE

import UI.Components.IconButton as IconButton

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Reason for dismissal (affects auto-focus behavior)
data DismissReason
  = EscapeKey    -- Normal close, auto-focus trigger
  | ClickOutside -- Prevent auto-focus (user clicked elsewhere)
  | CloseButton  -- User clicked close button

-- | Popover input props
type Input =
  { title :: Maybe String
  , description :: Maybe String
  , isOpen :: Boolean
  , defaultOpen :: Boolean
  , modal :: Boolean
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { title: Nothing
  , description: Nothing
  , isOpen: false
  , defaultOpen: false
  , modal: false
  , className: Nothing
  }

-- | Output events
data Output
  = OpenChanged Boolean
  | Dismissed DismissReason

-- | Queries for external control
data Query a
  = Open a
  | Close a
  | Toggle a
  | IsOpen (Boolean -> a)

-- | Internal state
type State =
  { input :: Input
  , isOpen :: Boolean
  , dismissReason :: Maybe DismissReason
  }

-- | Internal actions
data Action
  = Initialize
  | HandleTriggerClick
  | HandleCloseClick
  | HandleKeyDown KE.KeyboardEvent
  | HandleClickOutside
  | SetOpen Boolean
  | Receive Input

-- | Slot type for parent components
type Slot id = H.Slot Query Output id

-- | Child slots
type Slots = 
  ( closeButton :: H.Slot IconButton.Query IconButton.Output Unit
  )

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
  , isOpen: input.isOpen || input.defaultOpen
  , dismissReason: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ HP.attr (HH.AttrName "data-component") "popover-root"
    , HP.attr (HH.AttrName "data-open") (if state.isOpen then "true" else "false")
    , HP.attr (HH.AttrName "style") "position: relative; display: inline-block;"
    ]
    [ renderTrigger state
    , if state.isOpen then renderContent state else HH.text ""
    ]

renderTrigger :: forall m. State -> H.ComponentHTML Action Slots m
renderTrigger _ =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "popover-trigger"
    , HP.ref (H.RefLabel "trigger")
    , HE.onClick \_ -> HandleTriggerClick
    ]
    []  -- Trigger content provided by parent via slot

renderContent :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    [ HP.attr (HH.AttrName "data-component") "popover-content"
    , HP.attr (HH.AttrName "role") "dialog"
    , HP.attr (HH.AttrName "aria-modal") (if state.input.modal then "true" else "false")
    , HP.ref (H.RefLabel "content")
    , HP.attr (HH.AttrName "style") contentStyle
    , HP.tabIndex 0
    , HE.onKeyDown HandleKeyDown
    ]
    (headerSection state <> 
     descriptionSection state <> 
     [ bodySection ])
  where
    contentStyle = "position: absolute; top: 100%; left: 0; margin-top: 4px; z-index: 1000;"

headerSection :: forall m. MonadAff m => State -> Array (H.ComponentHTML Action Slots m)
headerSection state =
  case state.input.title of
    Nothing -> []
    Just titleText ->
      [ HH.div
          [ HP.attr (HH.AttrName "data-slot") "popover-header" ]
          [ HH.h3
              [ HP.attr (HH.AttrName "data-slot") "popover-title" ]
              [ HH.text titleText ]
          , HH.slot (Proxy :: Proxy "closeButton") unit IconButton.component
              { icon: "close"
              , size: IconButton.Normal
              , iconSize: Nothing
              , variant: IconButton.Ghost
              , disabled: false
              , ariaLabel: "Close"
              , className: Nothing
              }
              handleCloseOutput
          ]
      ]

handleCloseOutput :: IconButton.Output -> Action
handleCloseOutput IconButton.Clicked = HandleCloseClick

descriptionSection :: forall m. State -> Array (H.ComponentHTML Action Slots m)
descriptionSection state =
  case state.input.description of
    Nothing -> []
    Just desc ->
      [ HH.p
          [ HP.attr (HH.AttrName "data-slot") "popover-description" ]
          [ HH.text desc ]
      ]

bodySection :: forall m. H.ComponentHTML Action Slots m
bodySection =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "popover-body" ]
    []  -- Body content provided by parent

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Focus content when opened
    state <- H.get
    when state.isOpen focusContent

  HandleTriggerClick -> do
    state <- H.get
    let newOpen = not state.isOpen
    H.modify_ _ { isOpen = newOpen, dismissReason = Nothing }
    H.raise (OpenChanged newOpen)
    when newOpen focusContent

  HandleCloseClick -> do
    H.modify_ _ { isOpen = false, dismissReason = Just CloseButton }
    H.raise (OpenChanged false)
    H.raise (Dismissed CloseButton)
    focusTrigger

  HandleKeyDown ke -> do
    when (KE.key ke == "Escape") do
      liftEffect $ KE.preventDefault ke
      liftEffect $ KE.stopPropagation ke
      H.modify_ _ { isOpen = false, dismissReason = Just EscapeKey }
      H.raise (OpenChanged false)
      H.raise (Dismissed EscapeKey)
      focusTrigger

  HandleClickOutside -> do
    H.modify_ _ { isOpen = false, dismissReason = Just ClickOutside }
    H.raise (OpenChanged false)
    H.raise (Dismissed ClickOutside)
    -- Don't auto-focus trigger when clicking outside

  SetOpen open -> do
    H.modify_ _ { isOpen = open, dismissReason = Nothing }
    H.raise (OpenChanged open)
    when open focusContent

  Receive newInput -> do
    oldState <- H.get
    let shouldOpen = newInput.isOpen && not oldState.isOpen
    H.modify_ _ { input = newInput, isOpen = newInput.isOpen }
    when shouldOpen focusContent

-- Helper to focus content
focusContent :: forall m. MonadAff m => H.HalogenM State Action Slots Output m Unit
focusContent = do
  mEl <- H.getHTMLElementRef (H.RefLabel "content")
  case mEl of
    Just el -> liftEffect $ HTMLElement.focus el
    Nothing -> pure unit

-- Helper to focus trigger
focusTrigger :: forall m. MonadAff m => H.HalogenM State Action Slots Output m Unit
focusTrigger = do
  state <- H.get
  -- Only auto-focus if not dismissed by clicking outside
  case state.dismissReason of
    Just ClickOutside -> pure unit
    _ -> do
      mEl <- H.getHTMLElementRef (H.RefLabel "trigger")
      case mEl of
        Just el -> liftEffect $ HTMLElement.focus el
        Nothing -> pure unit

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  Open a -> do
    handleAction (SetOpen true)
    pure (Just a)

  Close a -> do
    handleAction (SetOpen false)
    pure (Just a)

  Toggle a -> do
    state <- H.get
    handleAction (SetOpen (not state.isOpen))
    pure (Just a)

  IsOpen reply -> do
    state <- H.get
    pure (Just (reply state.isOpen))

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs.
-- Positioning is handled via CSS.
-- Focus management uses Halogen refs.
-- Keyboard events are handled by Halogen event handlers.
--
-- Note: Click-outside detection would require FFI for document-level
-- event listeners. For now, the parent component should handle this
-- by passing isOpen=false when appropriate.
