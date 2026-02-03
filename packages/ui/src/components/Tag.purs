-- | Tag Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/tag.tsx (23 lines)
-- |
-- | Small text label/badge component.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-component="tag"` - Root element
-- | - `data-size="normal|large"` - Size variant
module UI.Components.Tag
  ( component
  , Input
  , TagSize(..)
  , defaultInput
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tag size variants
data TagSize
  = Normal
  | Large

derive instance eqTagSize :: Eq TagSize

sizeToString :: TagSize -> String
sizeToString Normal = "normal"
sizeToString Large = "large"

-- | Tag input props
type Input =
  { text :: String
  , size :: TagSize
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { text: ""
  , size: Normal
  , className: Nothing
  }

-- | Internal state (stateless component)
type State = { input :: Input }

-- | Internal actions
data Action = Receive Input

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

component :: forall q o m. MonadAff m => H.Component q Input o m
component = H.mkComponent
  { initialState: \input -> { input }
  , render
  , eval: H.mkEval $ H.defaultEval
      { receive = Just <<< Receive
      }
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.span
    ([ HP.attr (HH.AttrName "data-component") "tag"
     , HP.attr (HH.AttrName "data-size") (sizeToString state.input.size)
     ] <> classAttr state.input.className)
    [ HH.text state.input.text ]

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component is a simple styled span.
