-- | Select Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/select.tsx (170 lines)
-- |
-- | Dropdown select with grouping and highlight callbacks.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | Root:
-- | - `data-component="select"` - Root element
-- | - `data-trigger-style="settings"` - When using settings variant
-- | - `data-open="true|false"` - Open state
-- |
-- | Trigger:
-- | - `data-slot="select-trigger"` - Trigger button
-- | - `data-slot="select-trigger-value"` - Selected value display
-- | - `data-slot="select-trigger-icon"` - Dropdown icon
-- |
-- | Content:
-- | - `data-component="select-content"` - Dropdown content
-- | - `data-slot="select-content-list"` - Options list
-- | - `data-slot="select-section"` - Group section
-- |
-- | Items:
-- | - `data-slot="select-item"` - Option item
-- | - `data-slot="select-item-label"` - Item label
-- | - `data-slot="select-item-indicator"` - Check indicator
-- | - `data-highlighted="true"` - Highlighted item
module UI.Components.Select
  ( component
  , Query(..)
  , Input
  , Output(..)
  , SelectOption
  , SelectGroup
  , TriggerVariant(..)
  , Slot
  , defaultInput
  ) where

import Prelude

import Data.Array (filter, groupBy, mapWithIndex, nubBy)
import Data.Const (Const)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Void (Void)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Type.Proxy (Proxy(..))
import Web.UIEvent.KeyboardEvent as KE

import UI.Components.Icon as Icon

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Option configuration
type SelectOption =
  { value :: String
  , label :: String
  , group :: Maybe String
  }

-- | Grouped options
type SelectGroup =
  { category :: String
  , options :: Array SelectOption
  }

-- | Trigger visual variants
data TriggerVariant
  = Default
  | Settings

derive instance eqTriggerVariant :: Eq TriggerVariant

variantToString :: TriggerVariant -> String
variantToString Default = "default"
variantToString Settings = "settings"

-- | Select input props
type Input =
  { options :: Array SelectOption
  , selected :: Maybe String          -- Currently selected value
  , placeholder :: String
  , triggerVariant :: TriggerVariant
  , disabled :: Boolean
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { options: []
  , selected: Nothing
  , placeholder: "Select..."
  , triggerVariant: Default
  , disabled: false
  , className: Nothing
  }

-- | Output events
data Output
  = Selected String                   -- Value of selected option
  | Highlighted (Maybe String)        -- Value of highlighted option (for preview)
  | OpenChanged Boolean

-- | Queries for external control
data Query a
  = Open a
  | Close a
  | Toggle a
  | GetSelected (Maybe String -> a)
  | SetSelected String a

-- | Internal state
type State =
  { input :: Input
  , isOpen :: Boolean
  , highlightedValue :: Maybe String
  , selectedValue :: Maybe String
  }

-- | Internal actions
data Action
  = Initialize
  | HandleTriggerClick
  | HandleItemClick String
  | HandleItemHover String
  | HandleKeyDown KE.KeyboardEvent
  | CloseDropdown
  | Receive Input

-- | Slot type for parent components
type Slot id = H.Slot Query Output id

-- | Child slots
type Slots = ( icon :: H.Slot (Const Void) Void String )

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
  , isOpen: false
  , highlightedValue: Nothing
  , selectedValue: input.selected
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ HP.attr (HH.AttrName "data-component") "select"
    , HP.attr (HH.AttrName "data-trigger-style") (variantToString state.input.triggerVariant)
    , HP.attr (HH.AttrName "data-open") (if state.isOpen then "true" else "false")
    , HP.attr (HH.AttrName "style") "position: relative; display: inline-block;"
    , HE.onKeyDown HandleKeyDown
    ]
    [ renderTrigger state
    , if state.isOpen then renderContent state else HH.text ""
    ]

renderTrigger :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderTrigger state =
  let selectedLabel = findLabel state.selectedValue state.input.options
      displayText = fromMaybe state.input.placeholder selectedLabel
      iconName = case state.input.triggerVariant of
        Settings -> "chevron-down"
        Default -> "chevron-down"
  in
    HH.button
      [ HP.attr (HH.AttrName "data-slot") "select-trigger"
      , HP.type_ HP.ButtonButton
      , HP.disabled state.input.disabled
      , HP.attr (HH.AttrName "aria-haspopup") "listbox"
      , HP.attr (HH.AttrName "aria-expanded") (if state.isOpen then "true" else "false")
      , HE.onClick \_ -> HandleTriggerClick
      ]
      [ HH.span
          [ HP.attr (HH.AttrName "data-slot") "select-trigger-value" ]
          [ HH.text displayText ]
      , HH.span
          [ HP.attr (HH.AttrName "data-slot") "select-trigger-icon" ]
          [ HH.slot_ (Proxy :: Proxy "icon") "trigger" Icon.component
              { name: iconName
              , size: Icon.Small
              , className: Nothing
              }
          ]
      ]

renderContent :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderContent state =
  let groups = groupOptions state.input.options
      placement = case state.input.triggerVariant of
        Settings -> "position: absolute; top: 100%; right: 0; margin-top: 4px; z-index: 1000;"
        Default -> "position: absolute; top: 100%; left: 0; margin-top: 4px; z-index: 1000;"
  in
    HH.div
      ([ HP.attr (HH.AttrName "data-component") "select-content"
       , HP.attr (HH.AttrName "data-trigger-style") (variantToString state.input.triggerVariant)
       , HP.attr (HH.AttrName "role") "listbox"
       , HP.attr (HH.AttrName "style") placement
       , HP.tabIndex 0
       ] <> classAttr state.input.className)
      [ HH.div
          [ HP.attr (HH.AttrName "data-slot") "select-content-list" ]
          (map (renderGroup state) groups)
      ]

-- | Group options by their group field
groupOptions :: Array SelectOption -> Array SelectGroup
groupOptions opts =
  let -- Get unique groups in order
      uniqueGroups = nubBy (\a b -> a == b) (map (fromMaybe "" <<< _.group) opts)
  in map (\cat -> 
       { category: cat
       , options: filter (\o -> fromMaybe "" o.group == cat) opts
       }) uniqueGroups

renderGroup :: forall m. MonadAff m => State -> SelectGroup -> H.ComponentHTML Action Slots m
renderGroup state group =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "select-section" ]
    ([ if group.category == ""
       then HH.text ""
       else HH.div
         [ HP.attr (HH.AttrName "data-slot") "select-section-label" ]
         [ HH.text group.category ]
     ] <> map (renderOption state) group.options)

renderOption :: forall m. MonadAff m => State -> SelectOption -> H.ComponentHTML Action Slots m
renderOption state opt =
  let isSelected = state.selectedValue == Just opt.value
      isHighlighted = state.highlightedValue == Just opt.value
  in
    HH.div
      [ HP.attr (HH.AttrName "data-slot") "select-item"
      , HP.attr (HH.AttrName "role") "option"
      , HP.attr (HH.AttrName "data-value") opt.value
      , HP.attr (HH.AttrName "aria-selected") (if isSelected then "true" else "false")
      , HP.attr (HH.AttrName "data-highlighted") (if isHighlighted then "true" else "false")
      , HP.tabIndex (if isHighlighted then 0 else (-1))
      , HE.onClick \_ -> HandleItemClick opt.value
      , HE.onMouseEnter \_ -> HandleItemHover opt.value
      ]
      [ HH.span
          [ HP.attr (HH.AttrName "data-slot") "select-item-label" ]
          [ HH.text opt.label ]
      , if isSelected
          then HH.span
            [ HP.attr (HH.AttrName "data-slot") "select-item-indicator" ]
            [ HH.slot_ (Proxy :: Proxy "icon") opt.value Icon.component
                { name: "check"
                , size: Icon.Small
                , className: Nothing
                }
            ]
          else HH.text ""
      ]

-- Helper to find label for a value
findLabel :: Maybe String -> Array SelectOption -> Maybe String
findLabel Nothing _ = Nothing
findLabel (Just val) opts = 
  case filter (\o -> o.value == val) opts of
    [opt] -> Just opt.label
    _ -> Nothing

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize ->
    pure unit

  HandleTriggerClick -> do
    state <- H.get
    unless state.input.disabled do
      let newOpen = not state.isOpen
      H.modify_ _ { isOpen = newOpen, highlightedValue = Nothing }
      H.raise (OpenChanged newOpen)

  HandleItemClick value -> do
    H.modify_ _ { selectedValue = Just value, isOpen = false, highlightedValue = Nothing }
    H.raise (Selected value)
    H.raise (OpenChanged false)

  HandleItemHover value -> do
    H.modify_ _ { highlightedValue = Just value }
    H.raise (Highlighted (Just value))

  HandleKeyDown ke -> do
    state <- H.get
    when state.isOpen do
      case KE.key ke of
        "Escape" -> do
          liftEffect $ KE.preventDefault ke
          H.modify_ _ { isOpen = false, highlightedValue = Nothing }
          H.raise (OpenChanged false)
        
        "Enter" -> do
          liftEffect $ KE.preventDefault ke
          case state.highlightedValue of
            Just val -> handleAction (HandleItemClick val)
            Nothing -> pure unit
        
        "ArrowDown" -> do
          liftEffect $ KE.preventDefault ke
          moveHighlight 1
        
        "ArrowUp" -> do
          liftEffect $ KE.preventDefault ke
          moveHighlight (-1)
        
        _ -> pure unit

  CloseDropdown -> do
    H.modify_ _ { isOpen = false, highlightedValue = Nothing }
    H.raise (OpenChanged false)

  Receive newInput -> do
    H.modify_ _ 
      { input = newInput
      , selectedValue = newInput.selected
      }

-- Helper to move highlight up/down
moveHighlight :: forall m. MonadAff m => Int -> H.HalogenM State Action Slots Output m Unit
moveHighlight direction = do
  state <- H.get
  let opts = state.input.options
      values = map _.value opts
      total = arrayLength values
  when (total > 0) do
    let currentIdx = case state.highlightedValue of
          Nothing -> if direction > 0 then (-1) else total
          Just v -> fromMaybe (-1) (findIndex v values)
        newIdx = (currentIdx + direction) `mod` total
        normalizedIdx = if newIdx < 0 then total + newIdx else newIdx
    case arrayIndex values normalizedIdx of
      Just newVal -> do
        H.modify_ _ { highlightedValue = Just newVal }
        H.raise (Highlighted (Just newVal))
      Nothing -> pure unit

-- Array helpers
arrayLength :: forall a. Array a -> Int
arrayLength = arrayLengthImpl

findIndex :: String -> Array String -> Maybe Int
findIndex = findIndexImpl

arrayIndex :: forall a. Array a -> Int -> Maybe a
arrayIndex = arrayIndexImpl

foreign import arrayLengthImpl :: forall a. Array a -> Int
foreign import findIndexImpl :: String -> Array String -> Maybe Int
foreign import arrayIndexImpl :: forall a. Array a -> Int -> Maybe a

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  Open a -> do
    H.modify_ _ { isOpen = true, highlightedValue = Nothing }
    H.raise (OpenChanged true)
    pure (Just a)

  Close a -> do
    H.modify_ _ { isOpen = false, highlightedValue = Nothing }
    H.raise (OpenChanged false)
    pure (Just a)

  Toggle a -> do
    state <- H.get
    let newOpen = not state.isOpen
    H.modify_ _ { isOpen = newOpen, highlightedValue = Nothing }
    H.raise (OpenChanged newOpen)
    pure (Just a)

  GetSelected reply -> do
    state <- H.get
    pure (Just (reply state.selectedValue))

  SetSelected value a -> do
    H.modify_ _ { selectedValue = Just value }
    pure (Just a)

-- ═══════════════════════════════════════════════════════════════════════════════
-- MINIMAL FFI
-- ═══════════════════════════════════════════════════════════════════════════════
-- Array utilities
