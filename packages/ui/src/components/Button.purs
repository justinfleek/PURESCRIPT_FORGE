-- | Button Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/button.tsx (34 lines)
-- |
-- | Primary button component with variant and size support.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-component="button"` - Root element
-- | - `data-size="small|normal|large"` - Size variant
-- | - `data-variant="primary|secondary|ghost"` - Visual variant
-- | - `data-icon` - Present when button has an icon
module UI.Components.Button
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , ButtonSize(..)
  , ButtonVariant(..)
  , defaultInput
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
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

-- | Button size variants
data ButtonSize
  = Small
  | Normal
  | Large

derive instance eqButtonSize :: Eq ButtonSize

sizeToString :: ButtonSize -> String
sizeToString Small = "small"
sizeToString Normal = "normal"
sizeToString Large = "large"

-- | Button visual variants
data ButtonVariant
  = Primary
  | Secondary
  | Ghost

derive instance eqButtonVariant :: Eq ButtonVariant

variantToString :: ButtonVariant -> String
variantToString Primary = "primary"
variantToString Secondary = "secondary"
variantToString Ghost = "ghost"

-- | Button input props
type Input =
  { size :: ButtonSize
  , variant :: ButtonVariant
  , icon :: Maybe String           -- Icon name
  , disabled :: Boolean
  , label :: String                -- Button text
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { size: Normal
  , variant: Secondary
  , icon: Nothing
  , disabled: false
  , label: ""
  , className: Nothing
  }

-- | Output events
data Output
  = Clicked

-- | Queries for external control
data Query a
  = Focus a
  | Click a

-- | Internal state
type State =
  { input :: Input
  }

-- | Internal actions
data Action
  = HandleClick
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
initialState input = { input }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.button
    ([ HP.type_ HP.ButtonButton
    , HP.disabled state.input.disabled
    , HP.ref (H.RefLabel "button")
    , HP.attr (HH.AttrName "data-component") "button"
    , HP.attr (HH.AttrName "data-size") (sizeToString state.input.size)
    , HP.attr (HH.AttrName "data-variant") (variantToString state.input.variant)
    , HE.onClick \_ -> HandleClick
    ] <> iconAttr state.input.icon <> classAttr state.input.className)
    (iconElement state.input.icon <> [ HH.text state.input.label ])

-- | Conditionally add data-icon attribute
iconAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
iconAttr Nothing = []
iconAttr (Just name) = [ HP.attr (HH.AttrName "data-icon") name ]

-- | Conditionally add class
classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- | Render icon element if present
-- | In a full implementation, this would render an actual Icon component
iconElement :: forall w i. Maybe String -> Array (HH.HTML w i)
iconElement Nothing = []
iconElement (Just iconName) =
  [ HH.span
      [ HP.class_ (HH.ClassName "button-icon")
      , HP.attr (HH.AttrName "data-slot") "button-icon"
      , HP.attr (HH.AttrName "data-icon") iconName
      , HP.attr (HH.AttrName "aria-hidden") "true"
      ]
      []
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  HandleClick -> do
    state <- H.get
    unless state.input.disabled do
      H.raise Clicked

  Receive newInput -> do
    H.modify_ _ { input = newInput }

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  Focus a -> do
    mEl <- H.getHTMLElementRef (H.RefLabel "button")
    case mEl of
      Just el -> do
        liftEffect $ HTMLElement.focus el
        pure (Just a)
      Nothing -> pure (Just a)

  Click a -> do
    handleAction HandleClick
    pure (Just a)

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs:
-- - HTMLElement.focus from purescript-web-html
-- - No custom JavaScript required
