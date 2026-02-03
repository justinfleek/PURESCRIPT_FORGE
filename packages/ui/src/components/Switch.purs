-- | Switch Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/switch.tsx (30 lines)
-- |
-- | Toggle switch with label and description support.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-component="switch"` - Root element
-- | - `data-slot="switch-input"` - Hidden input
-- | - `data-slot="switch-label"` - Label text
-- | - `data-slot="switch-description"` - Description text
-- | - `data-slot="switch-control"` - Visual switch track
-- | - `data-slot="switch-thumb"` - Switch thumb/handle
-- | - `data-state="checked|unchecked"` - Switch state
module UI.Components.Switch
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , defaultInput
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Web.HTML.HTMLElement as HTMLElement

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Switch input props
type Input =
  { checked :: Maybe Boolean        -- Controlled checked state
  , defaultChecked :: Boolean       -- Initial state if uncontrolled
  , disabled :: Boolean
  , required :: Boolean
  , name :: Maybe String            -- Form input name
  , label :: Maybe String           -- Switch label
  , hideLabel :: Boolean            -- Hide label visually (sr-only)
  , description :: Maybe String     -- Description text
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { checked: Nothing
  , defaultChecked: false
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
  = CheckedChanged Boolean

-- | Queries for external control
data Query a
  = SetChecked Boolean a
  | GetChecked (Boolean -> a)
  | Toggle a

-- | Internal state
type State =
  { isChecked :: Boolean
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
  { isChecked: fromMaybe input.defaultChecked input.checked
  , input
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "switch"
    , HP.attr (HH.AttrName "data-state") (if state.isChecked then "checked" else "unchecked")
    ] <> classAttr state.input.className)
    [ renderHiddenInput state
    , renderLabel state
    , renderDescription state
    , renderControl state
    ]

renderHiddenInput :: forall m. State -> H.ComponentHTML Action () m
renderHiddenInput state =
  HH.input
    [ HP.type_ HP.InputCheckbox
    , HP.attr (HH.AttrName "data-slot") "switch-input"
    , HP.class_ (HH.ClassName "sr-only")
    , HP.checked state.isChecked
    , HP.disabled state.input.disabled
    , HP.required state.input.required
    ] <> nameAttr state.input.name

renderLabel :: forall m. State -> H.ComponentHTML Action () m
renderLabel state =
  case state.input.label of
    Nothing -> HH.text ""
    Just label ->
      HH.label
        ([ HP.attr (HH.AttrName "data-slot") "switch-label"
        ] <> srOnlyClass state.input.hideLabel)
        [ HH.text label ]

renderDescription :: forall m. State -> H.ComponentHTML Action () m
renderDescription state =
  case state.input.description of
    Nothing -> HH.text ""
    Just desc ->
      HH.span
        [ HP.attr (HH.AttrName "data-slot") "switch-description" ]
        [ HH.text desc ]

renderControl :: forall m. State -> H.ComponentHTML Action () m
renderControl state =
  HH.button
    [ HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "data-slot") "switch-control"
    , HP.attr (HH.AttrName "role") "switch"
    , HP.attr (HH.AttrName "aria-checked") (if state.isChecked then "true" else "false")
    , HP.disabled state.input.disabled
    , HP.ref (H.RefLabel "control")
    , HE.onClick \_ -> HandleClick
    ]
    [ HH.span
        [ HP.attr (HH.AttrName "data-slot") "switch-thumb"
        , HP.attr (HH.AttrName "data-state") (if state.isChecked then "checked" else "unchecked")
        ]
        []
    ]

-- Helper attribute functions
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
      Just newChecked -> H.modify_ _ { isChecked = newChecked }
      Nothing -> pure unit
    H.modify_ _ { input = newInput }

  HandleClick -> do
    state <- H.get
    unless state.input.disabled do
      let newChecked = not state.isChecked
      H.modify_ _ { isChecked = newChecked }
      H.raise (CheckedChanged newChecked)

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetChecked checked a -> do
    state <- H.get
    when (checked /= state.isChecked) do
      H.modify_ _ { isChecked = checked }
      H.raise (CheckedChanged checked)
    pure (Just a)

  GetChecked reply -> do
    state <- H.get
    pure (Just (reply state.isChecked))

  Toggle a -> do
    handleAction HandleClick
    pure (Just a)

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs.
-- No custom JavaScript required.
