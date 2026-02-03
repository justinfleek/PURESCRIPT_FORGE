-- | TextField Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/text-field.tsx (121 lines)
-- |
-- | Text input field with label, description, and copy functionality.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-component="input"` - Root element
-- | - `data-variant="normal|ghost"` - Visual variant
-- | - `data-slot="input-label"` - Label element
-- | - `data-slot="input-wrapper"` - Input container
-- | - `data-slot="input-input"` - The input/textarea element
-- | - `data-slot="input-copy-button"` - Copy button (when copyable)
-- | - `data-slot="input-description"` - Description text
-- | - `data-slot="input-error"` - Error message
module UI.Components.TextField
  ( component
  , Query(..)
  , Input
  , Output(..)
  , TextFieldVariant(..)
  , ValidationState(..)
  , Slot
  , defaultInput
  ) where

import Prelude

import Data.Const (Const)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Void (Void)
import Effect (Effect)
import Effect.Aff (Milliseconds(..), delay)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Type.Proxy (Proxy(..))
import Web.HTML.HTMLElement as HTMLElement

import UI.Components.Icon as Icon

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | TextField visual variants
data TextFieldVariant
  = Normal
  | Ghost

derive instance eqTextFieldVariant :: Eq TextFieldVariant

variantToString :: TextFieldVariant -> String
variantToString Normal = "normal"
variantToString Ghost = "ghost"

-- | Validation state
data ValidationState
  = Valid
  | Invalid

derive instance eqValidationState :: Eq ValidationState

validationToString :: ValidationState -> String
validationToString Valid = "valid"
validationToString Invalid = "invalid"

-- | TextField input props
type Input =
  { name :: Maybe String
  , value :: String
  , defaultValue :: Maybe String
  , placeholder :: Maybe String
  , label :: Maybe String
  , hideLabel :: Boolean
  , description :: Maybe String
  , errorMessage :: Maybe String
  , variant :: TextFieldVariant
  , copyable :: Boolean
  , multiline :: Boolean
  , required :: Boolean
  , disabled :: Boolean
  , readOnly :: Boolean
  , validationState :: Maybe ValidationState
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { name: Nothing
  , value: ""
  , defaultValue: Nothing
  , placeholder: Nothing
  , label: Nothing
  , hideLabel: false
  , description: Nothing
  , errorMessage: Nothing
  , variant: Normal
  , copyable: false
  , multiline: false
  , required: false
  , disabled: false
  , readOnly: false
  , validationState: Nothing
  , className: Nothing
  }

-- | Output events
data Output
  = ValueChanged String
  | Copied

-- | Queries for external control
data Query a
  = Focus a
  | GetValue (String -> a)
  | SetValue String a

-- | Internal state
type State =
  { input :: Input
  , currentValue :: String
  , showCopied :: Boolean
  }

-- | Internal actions
data Action
  = HandleInput String
  | HandleKeyDown
  | HandleCopy
  | HideCopied
  | Receive Input

-- | Slot type for parent components
type Slot id = H.Slot Query Output id

-- | Child slots
type Slots = ( copyIcon :: H.Slot (Const Void) Void Unit )

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
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { input
  , currentValue: fromMaybe input.value input.defaultValue
  , showCopied: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "input"
     , HP.attr (HH.AttrName "data-variant") (variantToString state.input.variant)
     ] <> validationAttr state.input.validationState
       <> classAttr state.input.className)
    (labelSection state <> 
     [ wrapperSection state ] <> 
     descriptionSection state <>
     errorSection state)

labelSection :: forall m. State -> Array (H.ComponentHTML Action Slots m)
labelSection state =
  case state.input.label of
    Nothing -> []
    Just labelText ->
      [ HH.label
          [ HP.attr (HH.AttrName "data-slot") "input-label"
          , HP.attr (HH.AttrName "class") (if state.input.hideLabel then "sr-only" else "")
          ]
          [ HH.text labelText ]
      ]

wrapperSection :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
wrapperSection state =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "input-wrapper"
    , HE.onClick \_ -> if state.input.copyable then HandleCopy else pure unit
    ]
    ([ renderInput state ] <> copyButton state)

renderInput :: forall m. State -> H.ComponentHTML Action Slots m
renderInput state =
  if state.input.multiline
    then renderTextarea state
    else renderInputField state

renderInputField :: forall m. State -> H.ComponentHTML Action Slots m
renderInputField state =
  HH.input
    ([ HP.type_ HP.InputText
     , HP.value state.currentValue
     , HP.disabled state.input.disabled
     , HP.readOnly state.input.readOnly
     , HP.required state.input.required
     , HP.ref (H.RefLabel "input")
     , HP.attr (HH.AttrName "data-slot") "input-input"
     , HE.onValueInput HandleInput
     ] <> nameAttr state.input.name
       <> placeholderAttr state.input.placeholder)

renderTextarea :: forall m. State -> H.ComponentHTML Action Slots m
renderTextarea state =
  HH.textarea
    ([ HP.value state.currentValue
     , HP.disabled state.input.disabled
     , HP.readOnly state.input.readOnly
     , HP.required state.input.required
     , HP.ref (H.RefLabel "input")
     , HP.attr (HH.AttrName "data-slot") "input-input"
     , HE.onValueInput HandleInput
     ] <> nameAttr state.input.name
       <> placeholderAttr state.input.placeholder)

copyButton :: forall m. MonadAff m => State -> Array (H.ComponentHTML Action Slots m)
copyButton state =
  if state.input.copyable
    then
      [ HH.button
          [ HP.type_ HP.ButtonButton
          , HP.attr (HH.AttrName "data-slot") "input-copy-button"
          , HP.attr (HH.AttrName "tabindex") "-1"
          , HP.attr (HH.AttrName "aria-label") (if state.showCopied then "Copied" else "Copy")
          , HE.onClick \_ -> HandleCopy
          ]
          [ HH.slot_ (Proxy :: Proxy "copyIcon") unit Icon.component
              { name: if state.showCopied then "check" else "copy"
              , size: Icon.Small
              , className: Nothing
              }
          ]
      ]
    else []

descriptionSection :: forall m. State -> Array (H.ComponentHTML Action Slots m)
descriptionSection state =
  case state.input.description of
    Nothing -> []
    Just desc ->
      [ HH.div
          [ HP.attr (HH.AttrName "data-slot") "input-description" ]
          [ HH.text desc ]
      ]

errorSection :: forall m. State -> Array (H.ComponentHTML Action Slots m)
errorSection state =
  case state.input.errorMessage of
    Nothing -> []
    Just err ->
      [ HH.div
          [ HP.attr (HH.AttrName "data-slot") "input-error"
          , HP.attr (HH.AttrName "role") "alert"
          ]
          [ HH.text err ]
      ]

-- Helper attribute functions
classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

nameAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
nameAttr Nothing = []
nameAttr (Just n) = [ HP.name n ]

placeholderAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
placeholderAttr Nothing = []
placeholderAttr (Just p) = [ HP.placeholder p ]

validationAttr :: forall r i. Maybe ValidationState -> Array (HP.IProp r i)
validationAttr Nothing = []
validationAttr (Just vs) = [ HP.attr (HH.AttrName "data-validation") (validationToString vs) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  HandleInput value -> do
    H.modify_ _ { currentValue = value }
    H.raise (ValueChanged value)

  HandleKeyDown ->
    pure unit  -- For future key handling

  HandleCopy -> do
    state <- H.get
    liftEffect $ copyToClipboard state.currentValue
    H.modify_ _ { showCopied = true }
    H.raise Copied
    -- Reset after 2 seconds
    liftAff $ delay (Milliseconds 2000.0)
    H.modify_ _ { showCopied = false }

  HideCopied ->
    H.modify_ _ { showCopied = false }

  Receive newInput -> do
    H.modify_ \st -> st
      { input = newInput
      , currentValue = if newInput.value /= st.input.value 
                       then newInput.value 
                       else st.currentValue
      }

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  Focus a -> do
    mEl <- H.getHTMLElementRef (H.RefLabel "input")
    case mEl of
      Just el -> liftEffect $ HTMLElement.focus el
      Nothing -> pure unit
    pure (Just a)

  GetValue reply -> do
    state <- H.get
    pure (Just (reply state.currentValue))

  SetValue value a -> do
    H.modify_ _ { currentValue = value }
    pure (Just a)

-- ═══════════════════════════════════════════════════════════════════════════════
-- FFI (Clipboard only - legitimate DOM operation)
-- ═══════════════════════════════════════════════════════════════════════════════

foreign import copyToClipboard :: String -> Effect Unit
