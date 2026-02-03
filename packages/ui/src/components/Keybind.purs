-- | Keybind Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/keybind.tsx (21 lines)
-- |
-- | Keyboard shortcut display component.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-component="keybind"` - Root span element
module UI.Components.Keybind
  ( component
  , Input
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

-- | Keybind input props
type Input =
  { keys :: String           -- The key combination text (e.g., "Ctrl+S")
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { keys: ""
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
    ([ HP.attr (HH.AttrName "data-component") "keybind"
     ] <> classAttr state.input.className)
    [ HH.text state.input.keys ]

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component is a simple styled span.
