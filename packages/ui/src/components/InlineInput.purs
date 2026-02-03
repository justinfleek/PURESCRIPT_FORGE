-- | InlineInput Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/inline-input.tsx (12 lines)
-- |
-- | Minimal inline input field.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-component="inline-input"` - Input element
module UI.Components.InlineInput
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
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Web.HTML.HTMLElement as HTMLElement

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | InlineInput input props
type Input =
  { value :: String
  , placeholder :: Maybe String
  , width :: Maybe String
  , disabled :: Boolean
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { value: ""
  , placeholder: Nothing
  , width: Nothing
  , disabled: false
  , className: Nothing
  }

-- | Output events
data Output
  = ValueChanged String
  | Submitted String

-- | Queries for external control
data Query a
  = Focus a
  | GetValue (String -> a)
  | SetValue String a

-- | Internal state
type State =
  { input :: Input
  , currentValue :: String
  }

-- | Internal actions
data Action
  = HandleInput String
  | HandleKeyDown String
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
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { input
  , currentValue: input.value
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.input
    ([ HP.type_ HP.InputText
     , HP.value state.currentValue
     , HP.disabled state.input.disabled
     , HP.ref (H.RefLabel "input")
     , HP.attr (HH.AttrName "data-component") "inline-input"
     , HE.onValueInput HandleInput
     , HE.onKeyDown \ke -> HandleKeyDown (keyFromEvent ke)
     ] <> placeholderAttr state.input.placeholder
       <> styleAttr state.input.width
       <> classAttr state.input.className)

-- | Extract key from keyboard event (simplified)
foreign import keyFromEvent :: forall e. e -> String

placeholderAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
placeholderAttr Nothing = []
placeholderAttr (Just p) = [ HP.placeholder p ]

styleAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
styleAttr Nothing = []
styleAttr (Just w) = [ HP.attr (HH.AttrName "style") ("width: " <> w <> ";") ]

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  HandleInput value -> do
    H.modify_ _ { currentValue = value }
    H.raise (ValueChanged value)

  HandleKeyDown key -> do
    when (key == "Enter") do
      state <- H.get
      H.raise (Submitted state.currentValue)

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

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
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
-- MINIMAL FFI
-- ═══════════════════════════════════════════════════════════════════════════════
-- Only keyboard event key extraction
