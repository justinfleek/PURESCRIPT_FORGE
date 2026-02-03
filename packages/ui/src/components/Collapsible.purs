-- | Collapsible Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/collapsible.tsx (47 lines)
-- |
-- | Expandable/collapsible content section.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Implements behavior from Radix/Kobalte Collapsible:
-- | - Controlled and uncontrolled modes
-- | - Keyboard support (Enter/Space to toggle)
-- | - ARIA attributes for accessibility
-- |
-- | Data Attributes:
-- | - `data-component="collapsible"` - Root element
-- | - `data-variant="normal|ghost"` - Visual variant
-- | - `data-slot="collapsible-trigger"` - Trigger element
-- | - `data-slot="collapsible-content"` - Content element
-- | - `data-slot="collapsible-arrow"` - Arrow indicator
-- | - `data-state="open|closed"` - Expansion state
module UI.Components.Collapsible
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , CollapsibleVariant(..)
  , defaultInput
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Collapsible visual variants
data CollapsibleVariant
  = Normal
  | Ghost

derive instance eqCollapsibleVariant :: Eq CollapsibleVariant

variantToString :: CollapsibleVariant -> String
variantToString Normal = "normal"
variantToString Ghost = "ghost"

-- | Collapsible input props
type Input =
  { open :: Maybe Boolean           -- Controlled open state
  , defaultOpen :: Boolean          -- Initial state if uncontrolled
  , disabled :: Boolean             -- Whether collapsible is disabled
  , variant :: CollapsibleVariant   -- Visual variant
  , triggerContent :: String        -- Text for trigger
  , panelContent :: String          -- Text for content panel
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { open: Nothing
  , defaultOpen: false
  , disabled: false
  , variant: Normal
  , triggerContent: ""
  , panelContent: ""
  , className: Nothing
  }

-- | Output events
data Output
  = OpenChanged Boolean

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
  | HandleTriggerClick

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
  { isOpen: fromMaybe input.defaultOpen input.open
  , input
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "collapsible"
    , HP.attr (HH.AttrName "data-variant") (variantToString state.input.variant)
    , HP.attr (HH.AttrName "data-state") (if state.isOpen then "open" else "closed")
    ] <> classAttr state.input.className)
    [ renderTrigger state
    , renderContent state
    ]

renderTrigger :: forall m. State -> H.ComponentHTML Action () m
renderTrigger state =
  HH.button
    [ HP.type_ HP.ButtonButton
    , HP.disabled state.input.disabled
    , HP.ref (H.RefLabel "trigger")
    , HP.attr (HH.AttrName "data-slot") "collapsible-trigger"
    , HP.attr (HH.AttrName "data-state") (if state.isOpen then "open" else "closed")
    , ARIA.expanded (show state.isOpen)
    , ARIA.controls "collapsible-content"
    , HE.onClick \_ -> HandleTriggerClick
    ]
    [ HH.span
        [ HP.attr (HH.AttrName "data-slot") "collapsible-arrow"
        , HP.attr (HH.AttrName "aria-hidden") "true"
        ]
        [ HH.text (if state.isOpen then "▼" else "▶") ]
    , HH.text state.input.triggerContent
    ]

renderContent :: forall m. State -> H.ComponentHTML Action () m
renderContent state =
  if state.isOpen then
    HH.div
      [ HP.id "collapsible-content"
      , HP.attr (HH.AttrName "data-slot") "collapsible-content"
      , HP.attr (HH.AttrName "data-state") "open"
      , HP.attr (HH.AttrName "role") "region"
      ]
      [ HH.text state.input.panelContent ]
  else
    HH.div
      [ HP.id "collapsible-content"
      , HP.attr (HH.AttrName "data-slot") "collapsible-content"
      , HP.attr (HH.AttrName "data-state") "closed"
      , HP.attr (HH.AttrName "role") "region"
      , HP.attr (HH.AttrName "hidden") "true"
      ]
      []

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

  HandleTriggerClick -> do
    state <- H.get
    unless state.input.disabled do
      let newOpen = not state.isOpen
      H.modify_ _ { isOpen = newOpen }
      H.raise (OpenChanged newOpen)

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  Open a -> do
    state <- H.get
    unless state.isOpen do
      H.modify_ _ { isOpen = true }
      H.raise (OpenChanged true)
    pure (Just a)

  Close a -> do
    state <- H.get
    when state.isOpen do
      H.modify_ _ { isOpen = false }
      H.raise (OpenChanged false)
    pure (Just a)

  Toggle a -> do
    handleAction HandleTriggerClick
    pure (Just a)

  IsOpen reply -> do
    state <- H.get
    pure (Just (reply state.isOpen))

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs.
-- No custom JavaScript required.
