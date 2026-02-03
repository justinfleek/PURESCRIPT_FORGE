-- | Accordion Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/accordion.tsx (93 lines)
-- |
-- | Collapsible accordion component with multiple items.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Implements behavior from Radix/Kobalte Accordion:
-- | - Single or multiple items open
-- | - Keyboard navigation (Arrow keys, Home, End)
-- | - ARIA attributes for accessibility
-- |
-- | Data Attributes:
-- | - `data-component="accordion"` - Root element
-- | - `data-slot="accordion-item"` - Individual item
-- | - `data-slot="accordion-header"` - Item header
-- | - `data-slot="accordion-trigger"` - Clickable trigger
-- | - `data-slot="accordion-content"` - Collapsible content
-- | - `data-state="open|closed"` - Item state
module UI.Components.Accordion
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , AccordionType(..)
  , AccordionItem
  , defaultInput
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (Maybe(..), fromMaybe)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Web.Event.Event as Event
import Web.HTML.HTMLElement as HTMLElement
import Web.UIEvent.KeyboardEvent as KE

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Accordion can allow single or multiple items open
data AccordionType
  = Single      -- Only one item open at a time
  | Multiple    -- Multiple items can be open

derive instance eqAccordionType :: Eq AccordionType

-- | An accordion item definition
type AccordionItem =
  { value :: String           -- Unique identifier
  , triggerContent :: String  -- Text for trigger button
  , panelContent :: String    -- Text for content panel
  , disabled :: Boolean       -- Whether item is disabled
  }

-- | Accordion input props
type Input =
  { items :: Array AccordionItem
  , accordionType :: AccordionType
  , value :: Maybe (Array String)     -- Controlled: which items are open
  , defaultValue :: Array String      -- Uncontrolled: initial open items
  , collapsible :: Boolean            -- Can all items be closed (single mode)
  , orientation :: Orientation
  , className :: Maybe String
  }

data Orientation = Horizontal | Vertical

derive instance eqOrientation :: Eq Orientation

defaultInput :: Input
defaultInput =
  { items: []
  , accordionType: Single
  , value: Nothing
  , defaultValue: []
  , collapsible: true
  , orientation: Vertical
  , className: Nothing
  }

-- | Output events
data Output
  = ValueChanged (Array String)

-- | Queries for external control
data Query a
  = Open String a           -- Open an item by value
  | Close String a          -- Close an item by value
  | Toggle String a         -- Toggle an item
  | GetValue (Array String -> a)

-- | Internal state
type State =
  { openItems :: Array String
  , input :: Input
  , baseId :: String
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | ToggleItem String
  | HandleKeyDown Int KE.KeyboardEvent  -- Index of focused trigger

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
  { openItems: fromMaybe input.defaultValue input.value
  , input
  , baseId: "accordion"  -- TODO: Generate unique ID
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "accordion"
    , HP.attr (HH.AttrName "data-orientation") (orientationStr state.input.orientation)
    ] <> classAttr state.input.className)
    (Array.mapWithIndex (renderItem state) state.input.items)

renderItem :: forall m. State -> Int -> AccordionItem -> H.ComponentHTML Action () m
renderItem state idx item =
  let
    isOpen = Array.elem item.value state.openItems
    triggerId = state.baseId <> "-trigger-" <> item.value
    contentId = state.baseId <> "-content-" <> item.value
    stateStr = if isOpen then "open" else "closed"
  in
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "accordion-item"
    , HP.attr (HH.AttrName "data-state") stateStr
    , HP.attr (HH.AttrName "data-disabled") (if item.disabled then "true" else "false")
    ]
    [ renderHeader state idx item isOpen triggerId contentId
    , renderContent state item isOpen triggerId contentId
    ]

renderHeader :: forall m. State -> Int -> AccordionItem -> Boolean -> String -> String -> H.ComponentHTML Action () m
renderHeader state idx item isOpen triggerId contentId =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "accordion-header" ]
    [ HH.button
        [ HP.type_ HP.ButtonButton
        , HP.id triggerId
        , HP.disabled item.disabled
        , HP.ref (H.RefLabel $ "trigger-" <> item.value)  -- Use Halogen ref for focus
        , HP.attr (HH.AttrName "data-slot") "accordion-trigger"
        , HP.attr (HH.AttrName "data-state") (if isOpen then "open" else "closed")
        , ARIA.expanded (show isOpen)
        , ARIA.controls contentId
        , HE.onClick \_ -> ToggleItem item.value
        , HE.onKeyDown (HandleKeyDown idx)
        ]
        [ HH.text item.triggerContent ]
    ]

renderContent :: forall m. State -> AccordionItem -> Boolean -> String -> String -> H.ComponentHTML Action () m
renderContent state item isOpen triggerId contentId =
  if isOpen then
    HH.div
      [ HP.id contentId
      , HP.attr (HH.AttrName "data-slot") "accordion-content"
      , HP.attr (HH.AttrName "data-state") "open"
      , HP.attr (HH.AttrName "role") "region"
      , ARIA.labelledBy triggerId
      ]
      [ HH.text item.panelContent ]
  else
    HH.div
      [ HP.id contentId
      , HP.attr (HH.AttrName "data-slot") "accordion-content"
      , HP.attr (HH.AttrName "data-state") "closed"
      , HP.attr (HH.AttrName "role") "region"
      , HP.attr (HH.AttrName "hidden") "true"
      , ARIA.labelledBy triggerId
      ]
      []

orientationStr :: Orientation -> String
orientationStr Horizontal = "horizontal"
orientationStr Vertical = "vertical"

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
    -- Handle controlled value
    case newInput.value of
      Just newValue -> H.modify_ _ { openItems = newValue }
      Nothing -> pure unit
    H.modify_ _ { input = newInput }

  ToggleItem value -> do
    state <- H.get
    -- Check if item is disabled
    let mItem = Array.find (\i -> i.value == value) state.input.items
    case mItem of
      Just item | item.disabled -> pure unit
      _ -> do
        let
          isCurrentlyOpen = Array.elem value state.openItems
          newOpenItems = case state.input.accordionType of
            Single ->
              if isCurrentlyOpen then
                if state.input.collapsible then [] else state.openItems
              else
                [value]
            Multiple ->
              if isCurrentlyOpen then
                Array.filter (_ /= value) state.openItems
              else
                state.openItems <> [value]
        
        H.modify_ _ { openItems = newOpenItems }
        H.raise (ValueChanged newOpenItems)

  HandleKeyDown currentIdx ke -> do
    state <- H.get
    let
      key = KE.key ke
      items = state.input.items
      enabledIndices = Array.mapWithIndex (\i item -> if item.disabled then Nothing else Just i) items
                       # Array.catMaybes
      currentEnabledIdx = Array.findIndex (_ == currentIdx) enabledIndices
      
      -- Navigate based on orientation and key
      nextIdx = case state.input.orientation, key of
        Vertical, "ArrowDown" -> nextEnabledItem enabledIndices currentEnabledIdx
        Vertical, "ArrowUp" -> prevEnabledItem enabledIndices currentEnabledIdx
        Horizontal, "ArrowRight" -> nextEnabledItem enabledIndices currentEnabledIdx
        Horizontal, "ArrowLeft" -> prevEnabledItem enabledIndices currentEnabledIdx
        _, "Home" -> Array.head enabledIndices
        _, "End" -> Array.last enabledIndices
        _, _ -> Nothing

    for_ nextIdx \idx -> do
      liftEffect $ Event.preventDefault (KE.toEvent ke)
      case Array.index items idx of
        Just item -> do
          -- Use Halogen's ref system - element exists by construction
          mEl <- H.getHTMLElementRef (H.RefLabel $ "trigger-" <> item.value)
          for_ mEl \el -> liftEffect $ HTMLElement.focus el
        Nothing -> pure unit

-- Helper to find next enabled item
nextEnabledItem :: Array Int -> Maybe Int -> Maybe Int
nextEnabledItem indices Nothing = Array.head indices
nextEnabledItem indices (Just current) =
  let next = current + 1
  in if next >= Array.length indices
     then Array.head indices  -- Loop to start
     else Array.index indices next

-- Helper to find previous enabled item
prevEnabledItem :: Array Int -> Maybe Int -> Maybe Int
prevEnabledItem indices Nothing = Array.last indices
prevEnabledItem indices (Just current) =
  let prev = current - 1
  in if prev < 0
     then Array.last indices  -- Loop to end
     else Array.index indices prev

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  Open value a -> do
    state <- H.get
    unless (Array.elem value state.openItems) do
      case state.input.accordionType of
        Single -> H.modify_ _ { openItems = [value] }
        Multiple -> H.modify_ _ { openItems = state.openItems <> [value] }
      newState <- H.get
      H.raise (ValueChanged newState.openItems)
    pure (Just a)

  Close value a -> do
    state <- H.get
    when (Array.elem value state.openItems) do
      let newItems = Array.filter (_ /= value) state.openItems
      -- In single mode with collapsible=false, can't close last item
      when (state.input.accordionType == Multiple || state.input.collapsible || not (Array.null newItems)) do
        H.modify_ _ { openItems = newItems }
        H.raise (ValueChanged newItems)
    pure (Just a)

  Toggle value a -> do
    handleAction (ToggleItem value)
    pure (Just a)

  GetValue reply -> do
    state <- H.get
    pure (Just (reply state.openItems))

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only Halogen's built-in ref system (H.getHTMLElementRef)
-- and standard Web APIs from purescript-web-html.
-- Elements exist by construction since we render them with HP.ref.
