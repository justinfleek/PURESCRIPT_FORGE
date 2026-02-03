-- | Tabs Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/tabs.tsx (119 lines)
-- |
-- | Tabbed interface with multiple variants.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Implements behavior from Radix/Kobalte Tabs:
-- | - Controlled and uncontrolled modes
-- | - Keyboard navigation (Arrow keys, Home, End)
-- | - Automatic or manual activation
-- | - ARIA attributes for accessibility
-- |
-- | Data Attributes:
-- | - `data-component="tabs"` - Root element
-- | - `data-variant="normal|alt|pill|settings"` - Visual variant
-- | - `data-orientation="horizontal|vertical"` - Layout direction
-- | - `data-slot="tabs-list"` - Tab bar container
-- | - `data-slot="tabs-trigger"` - Tab button
-- | - `data-slot="tabs-content"` - Content panel
-- | - `data-state="active|inactive"` - Tab selection state
module UI.Components.Tabs
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , TabsVariant(..)
  , TabsOrientation(..)
  , ActivationMode(..)
  , Tab
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

-- | Tabs visual variants
data TabsVariant
  = Normal
  | Alt
  | Pill
  | Settings

derive instance eqTabsVariant :: Eq TabsVariant

variantToString :: TabsVariant -> String
variantToString Normal = "normal"
variantToString Alt = "alt"
variantToString Pill = "pill"
variantToString Settings = "settings"

-- | Tabs orientation
data TabsOrientation
  = Horizontal
  | Vertical

derive instance eqTabsOrientation :: Eq TabsOrientation

orientationToString :: TabsOrientation -> String
orientationToString Horizontal = "horizontal"
orientationToString Vertical = "vertical"

-- | Activation mode
data ActivationMode
  = Automatic    -- Activate on focus
  | Manual       -- Activate on click/Enter only

derive instance eqActivationMode :: Eq ActivationMode

-- | A single tab definition
type Tab =
  { value :: String      -- Unique identifier
  , label :: String      -- Display label
  , disabled :: Boolean  -- Whether the tab is disabled
  , content :: String    -- Content to show when selected
  }

-- | Tabs input props
type Input =
  { tabs :: Array Tab
  , value :: Maybe String            -- Controlled value
  , defaultValue :: Maybe String     -- Default value (uncontrolled)
  , variant :: TabsVariant
  , orientation :: TabsOrientation
  , activationMode :: ActivationMode
  , loop :: Boolean                  -- Loop keyboard navigation
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { tabs: []
  , value: Nothing
  , defaultValue: Nothing
  , variant: Normal
  , orientation: Horizontal
  , activationMode: Automatic
  , loop: true
  , className: Nothing
  }

-- | Output events
data Output
  = ValueChanged String

-- | Queries for external control
data Query a
  = SetValue String a
  | GetValue (String -> a)

-- | Internal state
type State =
  { selectedValue :: String
  , input :: Input
  , baseId :: String
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | SelectTab String
  | HandleKeyDown Int KE.KeyboardEvent  -- Index of focused tab

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
  { selectedValue: getInitialValue input
  , input
  , baseId: "tabs"
  }
  where
  getInitialValue :: Input -> String
  getInitialValue i = 
    case i.value of
      Just v -> v
      Nothing -> case i.defaultValue of
        Just v -> v
        Nothing -> case Array.head (Array.filter (not <<< _.disabled) i.tabs) of
          Just tab -> tab.value
          Nothing -> ""

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "tabs"
    , HP.attr (HH.AttrName "data-variant") (variantToString state.input.variant)
    , HP.attr (HH.AttrName "data-orientation") (orientationToString state.input.orientation)
    ] <> classAttr state.input.className)
    [ renderTabList state
    , renderTabPanels state
    ]

renderTabList :: forall m. State -> H.ComponentHTML Action () m
renderTabList state =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "tabs-list"
    , HP.attr (HH.AttrName "role") "tablist"
    , HP.attr (HH.AttrName "aria-orientation") (orientationToString state.input.orientation)
    ]
    (Array.mapWithIndex (renderTab state) state.input.tabs)

renderTab :: forall m. State -> Int -> Tab -> H.ComponentHTML Action () m
renderTab state idx tab =
  let 
    isSelected = tab.value == state.selectedValue
    tabId = state.baseId <> "-tab-" <> tab.value
    panelId = state.baseId <> "-panel-" <> tab.value
  in
  HH.button
    [ HP.type_ HP.ButtonButton
    , HP.id tabId
    , HP.disabled tab.disabled
    , HP.tabIndex (if isSelected then 0 else (-1))
    , HP.ref (H.RefLabel $ "tab-" <> tab.value)  -- Halogen ref for focus
    , HP.attr (HH.AttrName "data-slot") "tabs-trigger"
    , HP.attr (HH.AttrName "role") "tab"
    , HP.attr (HH.AttrName "data-state") (if isSelected then "active" else "inactive")
    , HP.attr (HH.AttrName "data-disabled") (if tab.disabled then "true" else "false")
    , ARIA.selected (show isSelected)
    , ARIA.controls panelId
    , HE.onClick \_ -> SelectTab tab.value
    , HE.onKeyDown (HandleKeyDown idx)
    ]
    [ HH.text tab.label ]

renderTabPanels :: forall m. State -> H.ComponentHTML Action () m
renderTabPanels state =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "tabs-panels" ]
    (map (renderTabPanel state) state.input.tabs)

renderTabPanel :: forall m. State -> Tab -> H.ComponentHTML Action () m
renderTabPanel state tab =
  let
    isSelected = tab.value == state.selectedValue
    tabId = state.baseId <> "-tab-" <> tab.value
    panelId = state.baseId <> "-panel-" <> tab.value
  in
  if isSelected then
    HH.div
      [ HP.id panelId
      , HP.attr (HH.AttrName "data-slot") "tabs-content"
      , HP.attr (HH.AttrName "role") "tabpanel"
      , HP.tabIndex 0
      , HP.attr (HH.AttrName "data-state") "active"
      , ARIA.labelledBy tabId
      ]
      [ HH.text tab.content ]
  else
    HH.div
      [ HP.id panelId
      , HP.attr (HH.AttrName "data-slot") "tabs-content"
      , HP.attr (HH.AttrName "role") "tabpanel"
      , HP.tabIndex (-1)
      , HP.attr (HH.AttrName "data-state") "inactive"
      , HP.attr (HH.AttrName "hidden") "true"
      , ARIA.labelledBy tabId
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
    -- Handle controlled value changes
    case newInput.value of
      Just newValue -> do
        state <- H.get
        when (newValue /= state.selectedValue) do
          H.modify_ _ { selectedValue = newValue }
      Nothing -> pure unit
    H.modify_ _ { input = newInput }

  SelectTab value -> do
    state <- H.get
    -- Find the tab to check if disabled
    let mTab = Array.find (\t -> t.value == value) state.input.tabs
    case mTab of
      Just tab | not tab.disabled -> do
        H.modify_ _ { selectedValue = value }
        H.raise (ValueChanged value)
      _ -> pure unit

  HandleKeyDown currentIdx ke -> do
    state <- H.get
    let
      key = KE.key ke
      tabs = state.input.tabs
      enabledIndices = Array.mapWithIndex (\i t -> if t.disabled then Nothing else Just i) tabs
                       # Array.catMaybes
      currentEnabledIdx = Array.findIndex (_ == currentIdx) enabledIndices
      
      -- Navigate based on orientation and key
      nextIdx = case state.input.orientation, key of
        Horizontal, "ArrowRight" -> nextEnabledTab enabledIndices currentEnabledIdx state.input.loop
        Horizontal, "ArrowLeft" -> prevEnabledTab enabledIndices currentEnabledIdx state.input.loop
        Vertical, "ArrowDown" -> nextEnabledTab enabledIndices currentEnabledIdx state.input.loop
        Vertical, "ArrowUp" -> prevEnabledTab enabledIndices currentEnabledIdx state.input.loop
        _, "Home" -> Array.head enabledIndices
        _, "End" -> Array.last enabledIndices
        _, _ -> Nothing

    for_ nextIdx \idx -> do
      liftEffect $ Event.preventDefault (KE.toEvent ke)
      case Array.index tabs idx of
        Just tab -> do
          -- Focus the tab using Halogen refs
          mEl <- H.getHTMLElementRef (H.RefLabel $ "tab-" <> tab.value)
          for_ mEl \el -> liftEffect $ HTMLElement.focus el
          
          -- If automatic activation, select it too
          when (state.input.activationMode == Automatic) do
            handleAction (SelectTab tab.value)
        Nothing -> pure unit

-- Helper to find next enabled tab
nextEnabledTab :: Array Int -> Maybe Int -> Boolean -> Maybe Int
nextEnabledTab indices mCurrent loop =
  case mCurrent of
    Nothing -> Array.head indices
    Just current ->
      let next = current + 1
      in if next >= Array.length indices
         then if loop then Array.head indices else Nothing
         else Array.index indices next

-- Helper to find previous enabled tab
prevEnabledTab :: Array Int -> Maybe Int -> Boolean -> Maybe Int
prevEnabledTab indices mCurrent loop =
  case mCurrent of
    Nothing -> Array.last indices
    Just current ->
      let prev = current - 1
      in if prev < 0
         then if loop then Array.last indices else Nothing
         else Array.index indices prev

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetValue value a -> do
    handleAction (SelectTab value)
    pure (Just a)
  
  GetValue reply -> do
    state <- H.get
    pure (Just (reply state.selectedValue))

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only Halogen's built-in ref system (H.getHTMLElementRef)
-- and standard Web APIs from purescript-web-html.
-- Elements exist by construction since we render them with HP.ref.
