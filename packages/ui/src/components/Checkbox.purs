-- | Checkbox Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/checkbox.tsx (44 lines)
-- |
-- | Checkbox input with label and description support.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-component="checkbox"` - Root element
-- | - `data-slot="checkbox-input"` - Hidden input
-- | - `data-slot="checkbox-control"` - Visual checkbox
-- | - `data-slot="checkbox-indicator"` - Check mark
-- | - `data-slot="checkbox-content"` - Label/description container
-- | - `data-slot="checkbox-label"` - Label text
-- | - `data-slot="checkbox-description"` - Description text
-- | - `data-state="checked|unchecked|indeterminate"` - Checkbox state
module UI.Components.Checkbox
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , CheckboxState(..)
  , defaultInput
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Checkbox can be in three states
data CheckboxState
  = Checked
  | Unchecked
  | Indeterminate

derive instance eqCheckboxState :: Eq CheckboxState

stateToString :: CheckboxState -> String
stateToString Checked = "checked"
stateToString Unchecked = "unchecked"
stateToString Indeterminate = "indeterminate"

stateToBoolean :: CheckboxState -> Boolean
stateToBoolean Checked = true
stateToBoolean Unchecked = false
stateToBoolean Indeterminate = false  -- Treat as unchecked for form submission

-- | Checkbox input props
type Input =
  { checked :: Maybe CheckboxState  -- Controlled checked state
  , defaultChecked :: CheckboxState -- Initial state if uncontrolled
  , disabled :: Boolean
  , required :: Boolean
  , name :: Maybe String            -- Form input name
  , label :: Maybe String           -- Checkbox label
  , hideLabel :: Boolean            -- Hide label visually (sr-only)
  , description :: Maybe String     -- Description text
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { checked: Nothing
  , defaultChecked: Unchecked
  , disabled: false
  , required: false
  , name: Nothing
  , label: Nothing
  , hideLabel: false
  , description: Nothing
  , className: Nothing
  }

-- | Output events
data Output
  = CheckedChanged CheckboxState

-- | Queries for external control
data Query a
  = SetChecked CheckboxState a
  | GetChecked (CheckboxState -> a)
  | Toggle a

-- | Internal state
type State =
  { checkState :: CheckboxState
  , input :: Input
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleClick

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
  { checkState: fromMaybe input.defaultChecked input.checked
  , input
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "checkbox"
    , HP.attr (HH.AttrName "data-state") (stateToString state.checkState)
    ] <> classAttr state.input.className)
    [ renderHiddenInput state
    , renderControl state
    , renderContent state
    ]

renderHiddenInput :: forall m. State -> H.ComponentHTML Action () m
renderHiddenInput state =
  HH.input
    ([ HP.type_ HP.InputCheckbox
    , HP.attr (HH.AttrName "data-slot") "checkbox-input"
    , HP.class_ (HH.ClassName "sr-only")
    , HP.checked (stateToBoolean state.checkState)
    , HP.disabled state.input.disabled
    , HP.required state.input.required
    ] <> nameAttr state.input.name)

renderControl :: forall m. State -> H.ComponentHTML Action () m
renderControl state =
  HH.button
    [ HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "data-slot") "checkbox-control"
    , HP.attr (HH.AttrName "role") "checkbox"
    , HP.attr (HH.AttrName "aria-checked") (ariaChecked state.checkState)
    , HP.disabled state.input.disabled
    , HP.ref (H.RefLabel "control")
    , HE.onClick \_ -> HandleClick
    ]
    [ renderIndicator state ]

renderIndicator :: forall m. State -> H.ComponentHTML Action () m
renderIndicator state =
  case state.checkState of
    Unchecked -> HH.text ""
    Checked ->
      HH.span
        [ HP.attr (HH.AttrName "data-slot") "checkbox-indicator" ]
        [ -- SVG checkmark
          HH.element (HH.ElemName "svg")
            [ HP.attr (HH.AttrName "viewBox") "0 0 12 12"
            , HP.attr (HH.AttrName "fill") "none"
            , HP.attr (HH.AttrName "width") "10"
            , HP.attr (HH.AttrName "height") "10"
            ]
            [ HH.element (HH.ElemName "path")
                [ HP.attr (HH.AttrName "d") "M3 7.17905L5.02703 8.85135L9 3.5"
                , HP.attr (HH.AttrName "stroke") "currentColor"
                , HP.attr (HH.AttrName "stroke-width") "1.5"
                , HP.attr (HH.AttrName "stroke-linecap") "square"
                ]
                []
            ]
        ]
    Indeterminate ->
      HH.span
        [ HP.attr (HH.AttrName "data-slot") "checkbox-indicator" ]
        [ -- Indeterminate dash
          HH.element (HH.ElemName "svg")
            [ HP.attr (HH.AttrName "viewBox") "0 0 12 12"
            , HP.attr (HH.AttrName "fill") "none"
            , HP.attr (HH.AttrName "width") "10"
            , HP.attr (HH.AttrName "height") "10"
            ]
            [ HH.element (HH.ElemName "line")
                [ HP.attr (HH.AttrName "x1") "3"
                , HP.attr (HH.AttrName "y1") "6"
                , HP.attr (HH.AttrName "x2") "9"
                , HP.attr (HH.AttrName "y2") "6"
                , HP.attr (HH.AttrName "stroke") "currentColor"
                , HP.attr (HH.AttrName "stroke-width") "1.5"
                ]
                []
            ]
        ]

renderContent :: forall m. State -> H.ComponentHTML Action () m
renderContent state =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "checkbox-content" ]
    [ renderLabel state
    , renderDescription state
    ]

renderLabel :: forall m. State -> H.ComponentHTML Action () m
renderLabel state =
  case state.input.label of
    Nothing -> HH.text ""
    Just label ->
      HH.label
        ([ HP.attr (HH.AttrName "data-slot") "checkbox-label"
        ] <> srOnlyClass state.input.hideLabel)
        [ HH.text label ]

renderDescription :: forall m. State -> H.ComponentHTML Action () m
renderDescription state =
  case state.input.description of
    Nothing -> HH.text ""
    Just desc ->
      HH.span
        [ HP.attr (HH.AttrName "data-slot") "checkbox-description" ]
        [ HH.text desc ]

-- Helper attribute functions
ariaChecked :: CheckboxState -> String
ariaChecked Checked = "true"
ariaChecked Unchecked = "false"
ariaChecked Indeterminate = "mixed"

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

nameAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
nameAttr Nothing = []
nameAttr (Just n) = [ HP.name n ]

srOnlyClass :: forall r i. Boolean -> Array (HP.IProp r i)
srOnlyClass false = []
srOnlyClass true = [ HP.class_ (HH.ClassName "sr-only") ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive newInput -> do
    -- Handle controlled state
    case newInput.checked of
      Just newChecked -> H.modify_ _ { checkState = newChecked }
      Nothing -> pure unit
    H.modify_ _ { input = newInput }

  HandleClick -> do
    state <- H.get
    unless state.input.disabled do
      -- Toggle: Checked -> Unchecked, Unchecked -> Checked, Indeterminate -> Checked
      let newState = case state.checkState of
            Checked -> Unchecked
            Unchecked -> Checked
            Indeterminate -> Checked
      H.modify_ _ { checkState = newState }
      H.raise (CheckedChanged newState)

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetChecked checked a -> do
    state <- H.get
    when (checked /= state.checkState) do
      H.modify_ _ { checkState = checked }
      H.raise (CheckedChanged checked)
    pure (Just a)

  GetChecked reply -> do
    state <- H.get
    pure (Just (reply state.checkState))

  Toggle a -> do
    handleAction HandleClick
    pure (Just a)

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs.
-- No custom JavaScript required.
