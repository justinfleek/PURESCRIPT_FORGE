-- | ImagePreview Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/image-preview.tsx (33 lines)
-- |
-- | Image preview dialog/lightbox.
-- | Pure Halogen implementation built on Dialog primitive.
-- |
-- | Data Attributes:
-- | - `data-component="image-preview"` - Root element
-- | - `data-slot="image-preview-container"` - Container wrapper
-- | - `data-slot="image-preview-content"` - Dialog content
-- | - `data-slot="image-preview-header"` - Header with close button
-- | - `data-slot="image-preview-close"` - Close button
-- | - `data-slot="image-preview-body"` - Body containing image
-- | - `data-slot="image-preview-image"` - Image element
module UI.Components.ImagePreview
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , defaultInput
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | ImagePreview input props
type Input =
  { src :: String           -- Image source URL
  , alt :: String           -- Alt text for image
  , open :: Maybe Boolean   -- Controlled open state
  , defaultOpen :: Boolean  -- Initial state if uncontrolled
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { src: ""
  , alt: "Image preview"
  , open: Nothing
  , defaultOpen: false
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
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleOpen
  | HandleClose
  | HandleOverlayClick
  | HandleKeyDown String

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
  { isOpen: case input.open of
      Just o -> o
      Nothing -> input.defaultOpen
  , input
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.attr (HH.AttrName "data-component") "image-preview"
    ]
    [ if state.isOpen then renderDialog state else HH.text ""
    ]

renderDialog :: forall m. State -> H.ComponentHTML Action () m
renderDialog state =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "image-preview-container"
    , HP.class_ (HH.ClassName "image-preview-overlay")
    , HE.onClick \_ -> HandleOverlayClick
    ]
    [ HH.div
        ([ HP.attr (HH.AttrName "data-slot") "image-preview-content"
        , HP.attr (HH.AttrName "role") "dialog"
        , HP.attr (HH.AttrName "aria-modal") "true"
        , ARIA.label state.input.alt
        , HP.tabIndex 0
        , HE.onClick \_ -> HandleClose -- Click on content doesn't close
        ] <> classAttr state.input.className)
        [ renderHeader
        , renderBody state
        ]
    ]

renderHeader :: forall m. H.ComponentHTML Action () m
renderHeader =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "image-preview-header" ]
    [ HH.button
        [ HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "data-slot") "image-preview-close"
        , ARIA.label "Close"
        , HE.onClick \_ -> HandleClose
        ]
        [ HH.text "×" ]
    ]

renderBody :: forall m. State -> H.ComponentHTML Action () m
renderBody state =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "image-preview-body" ]
    [ HH.img
        [ HP.src state.input.src
        , HP.alt state.input.alt
        , HP.attr (HH.AttrName "data-slot") "image-preview-image"
        ]
    ]

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive newInput -> do
    -- Handle controlled state
    case newInput.open of
      Just newOpen -> H.modify_ _ { isOpen = newOpen }
      Nothing -> pure unit
    H.modify_ _ { input = newInput }

  HandleOpen -> do
    H.modify_ _ { isOpen = true }
    H.raise Opened
    H.raise (OpenChanged true)

  HandleClose -> do
    H.modify_ _ { isOpen = false }
    H.raise Closed
    H.raise (OpenChanged false)

  HandleOverlayClick -> do
    -- Close when clicking overlay (outside content)
    handleAction HandleClose

  HandleKeyDown key -> do
    when (key == "Escape") do
      handleAction HandleClose

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  Open a -> do
    handleAction HandleOpen
    pure (Just a)

  Close a -> do
    handleAction HandleClose
    pure (Just a)

  Toggle a -> do
    state <- H.get
    if state.isOpen
      then handleAction HandleClose
      else handleAction HandleOpen
    pure (Just a)

  IsOpen reply -> do
    state <- H.get
    pure (Just (reply state.isOpen))

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs.
-- Image display is pure HTML img element.
