-- | IconButton Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/icon-button.tsx (29 lines)
-- |
-- | Button with only an icon (no text label).
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-component="icon-button"` - Root element
-- | - `data-size="normal|large"` - Size variant
-- | - `data-variant="primary|secondary|ghost"` - Visual variant
module UI.Components.IconButton
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , IconButtonSize(..)
  , IconButtonVariant(..)
  , defaultInput
  ) where

import Prelude

import Data.Const (Const)
import Data.Maybe (Maybe(..))
import Data.Void (Void)
import Effect.Aff.Class (class MonadAff)
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

-- | IconButton size variants
data IconButtonSize
  = Normal
  | Large

derive instance eqIconButtonSize :: Eq IconButtonSize

sizeToString :: IconButtonSize -> String
sizeToString Normal = "normal"
sizeToString Large = "large"

-- | IconButton visual variants
data IconButtonVariant
  = Primary
  | Secondary
  | Ghost

derive instance eqIconButtonVariant :: Eq IconButtonVariant

variantToString :: IconButtonVariant -> String
variantToString Primary = "primary"
variantToString Secondary = "secondary"
variantToString Ghost = "ghost"

-- | IconButton input props
type Input =
  { icon :: Icon.IconName
  , size :: IconButtonSize
  , iconSize :: Maybe Icon.IconSize
  , variant :: IconButtonVariant
  , disabled :: Boolean
  , ariaLabel :: String            -- Required for accessibility
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { icon: "check"
  , size: Normal
  , iconSize: Nothing
  , variant: Secondary
  , disabled: false
  , ariaLabel: "Button"
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

-- | Child slots for Icon
type Slots = ( icon :: H.Slot (Const Void) Void Unit )

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

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.button
    ([ HP.type_ HP.ButtonButton
    , HP.disabled state.input.disabled
    , HP.ref (H.RefLabel "button")
    , HP.attr (HH.AttrName "data-component") "icon-button"
    , HP.attr (HH.AttrName "data-size") (sizeToString state.input.size)
    , HP.attr (HH.AttrName "data-variant") (variantToString state.input.variant)
    , HP.attr (HH.AttrName "aria-label") state.input.ariaLabel
    , HE.onClick \_ -> HandleClick
    ] <> classAttr state.input.className)
    [ HH.slot_ (Proxy :: Proxy "icon") unit Icon.component
        { name: state.input.icon
        , size: getIconSize state.input
        , className: Nothing
        }
    ]

-- | Determine icon size based on button size or explicit iconSize
getIconSize :: Input -> Icon.IconSize
getIconSize input =
  case input.iconSize of
    Just size -> size
    Nothing ->
      case input.size of
        Large -> Icon.Normal
        Normal -> Icon.Small

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
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

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
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
-- This component uses only standard Halogen/Web APIs.
-- No custom JavaScript required.
