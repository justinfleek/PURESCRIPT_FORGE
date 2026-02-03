-- | Card Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/card.tsx (23 lines)
-- |
-- | Container card with status variant support.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-component="card"` - Root element
-- | - `data-variant="normal|error|warning|success|info"` - Visual variant
module UI.Components.Card
  ( component
  , Input
  , CardVariant(..)
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

-- | Card visual variants for status indication
data CardVariant
  = Normal
  | Error
  | Warning
  | Success
  | Info

derive instance eqCardVariant :: Eq CardVariant

variantToString :: CardVariant -> String
variantToString Normal = "normal"
variantToString Error = "error"
variantToString Warning = "warning"
variantToString Success = "success"
variantToString Info = "info"

-- | Card input props
type Input =
  { variant :: CardVariant
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { variant: Normal
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
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "card"
     , HP.attr (HH.AttrName "data-variant") (variantToString state.input.variant)
     ] <> classAttr state.input.className)
    []  -- Children provided by parent via slot

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component is a simple styled container div.
