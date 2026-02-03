-- | RadioGroup Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/radio-group.tsx (76 lines)
-- |
-- | Segmented control / radio button group.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-component="radio-group"` - Root element
-- | - `data-size="small|medium"` - Size variant
-- | - `data-slot="radio-group-wrapper"` - Outer wrapper
-- | - `data-slot="radio-group-indicator"` - Selection indicator
-- | - `data-slot="radio-group-items"` - Items container
-- | - `data-slot="radio-group-item"` - Individual option
-- | - `data-state="checked|unchecked"` - Selection state per item
module UI.Components.RadioGroup
  ( component
  , Query(..)
  , Input
  , Output(..)
  , RadioGroupSize(..)
  , Slot
  , defaultInput
  ) where

import Prelude

import Data.Array (findIndex, length, mapWithIndex)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | RadioGroup size variants
data RadioGroupSize
  = Small
  | Medium

derive instance eqRadioGroupSize :: Eq RadioGroupSize

sizeToString :: RadioGroupSize -> String
sizeToString Small = "small"
sizeToString Medium = "medium"

-- | Option configuration
type Option =
  { value :: String
  , label :: String
  }

-- | RadioGroup input props
type Input =
  { options :: Array Option
  , selected :: Maybe String           -- Currently selected value
  , defaultValue :: Maybe String       -- Initial value if selected is Nothing
  , size :: RadioGroupSize
  , disabled :: Boolean
  , name :: String                     -- Form name for hidden inputs
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { options: []
  , selected: Nothing
  , defaultValue: Nothing
  , size: Medium
  , disabled: false
  , name: "radio-group"
  , className: Nothing
  }

-- | Output events
data Output
  = Selected String  -- Value of selected option

-- | Queries for external control
data Query a
  = GetSelected (Maybe String -> a)
  | SetSelected String a

-- | Internal state
type State =
  { input :: Input
  , currentValue :: Maybe String
  }

-- | Internal actions
data Action
  = Initialize
  | SelectOption String
  | Receive Input

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
  , currentValue: input.selected <|> input.defaultValue
  }
  where
    -- Maybe's Alt instance for fallback
    (<|>) :: forall a. Maybe a -> Maybe a -> Maybe a
    (<|>) (Just x) _ = Just x
    (<|>) Nothing y = y

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "radio-group"
     , HP.attr (HH.AttrName "data-size") (sizeToString state.input.size)
     , HP.attr (HH.AttrName "role") "radiogroup"
     , HP.ref (H.RefLabel "root")
     ] <> disabledAttr state.input.disabled <> classAttr state.input.className)
    [ HH.div
        [ HP.attr (HH.AttrName "role") "presentation"
        , HP.attr (HH.AttrName "data-slot") "radio-group-wrapper"
        ]
        [ renderIndicator state
        , HH.div
            [ HP.attr (HH.AttrName "role") "presentation"
            , HP.attr (HH.AttrName "data-slot") "radio-group-items"
            ]
            (mapWithIndex (renderOption state) state.input.options)
        ]
    ]

-- | Render the sliding indicator that shows current selection
renderIndicator :: forall m. State -> H.ComponentHTML Action () m
renderIndicator state =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "radio-group-indicator"
    , HP.attr (HH.AttrName "style") (indicatorStyle state)
    , HP.attr (HH.AttrName "aria-hidden") "true"
    ]
    []

-- | Calculate indicator position based on selected index
indicatorStyle :: State -> String
indicatorStyle state =
  case state.currentValue of
    Nothing -> "opacity: 0;"
    Just val ->
      let mIdx = findIndex (\opt -> opt.value == val) state.input.options
          count = length state.input.options
      in case mIdx of
        Nothing -> "opacity: 0;"
        Just idx ->
          let percent = if count > 0 
                        then (toNumber idx / toNumber count) * 100.0
                        else 0.0
              width = if count > 0
                      then 100.0 / toNumber count
                      else 100.0
          in "transform: translateX(" <> show percent <> "%); width: " <> show width <> "%;"

-- | Render a single radio option
renderOption :: forall m. State -> Int -> Option -> H.ComponentHTML Action () m
renderOption state idx opt =
  let isChecked = state.currentValue == Just opt.value
      stateStr = if isChecked then "checked" else "unchecked"
  in
    HH.label
      [ HP.attr (HH.AttrName "data-slot") "radio-group-item"
      , HP.attr (HH.AttrName "data-state") stateStr
      , HP.attr (HH.AttrName "data-index") (show idx)
      ]
      [ -- Hidden native radio input for form compatibility
        HH.input
          [ HP.type_ HP.InputRadio
          , HP.name state.input.name
          , HP.value opt.value
          , HP.checked isChecked
          , HP.disabled state.input.disabled
          , HP.attr (HH.AttrName "data-slot") "radio-group-item-input"
          , HP.attr (HH.AttrName "style") "position: absolute; opacity: 0; pointer-events: none;"
          , HE.onChange \_ -> SelectOption opt.value
          ]
      , HH.span
          [ HP.attr (HH.AttrName "data-slot") "radio-group-item-label" ]
          [ HH.text opt.label ]
      ]

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

disabledAttr :: forall r i. Boolean -> Array (HP.IProp r i)
disabledAttr false = []
disabledAttr true = [ HP.attr (HH.AttrName "aria-disabled") "true" ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize ->
    pure unit

  SelectOption value -> do
    state <- H.get
    unless state.input.disabled do
      H.modify_ _ { currentValue = Just value }
      H.raise (Selected value)

  Receive newInput -> do
    H.modify_ \st -> st
      { input = newInput
      , currentValue = newInput.selected <|> st.currentValue
      }
    where
      (<|>) :: forall a. Maybe a -> Maybe a -> Maybe a
      (<|>) (Just x) _ = Just x
      (<|>) Nothing y = y

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  GetSelected reply -> do
    state <- H.get
    pure (Just (reply state.currentValue))

  SetSelected value a -> do
    H.modify_ _ { currentValue = Just value }
    pure (Just a)

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs.
-- Selection state is managed in Halogen state.
-- Indicator position is calculated from array index.
