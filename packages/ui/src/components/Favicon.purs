-- | Favicon Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/favicon.tsx (14 lines)
-- |
-- | Injects favicon and web app manifest links into document head.
-- | This is a side-effect component that adds meta tags on initialization.
-- |
-- | Assets referenced:
-- | - /favicon-96x96-v3.png
-- | - /favicon-v3.ico
-- | - /apple-touch-icon-v3.png
-- | - /site.webmanifest
module UI.Components.Favicon
  ( component
  , installFavicon
  ) where

import Prelude

import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- No input needed - this is a fire-and-forget component
type Input = Unit

-- | Internal state
type State = { installed :: Boolean }

-- | Internal actions
data Action = Initialize

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Halogen component that installs favicon on mount
-- | Renders nothing - just performs the side effect
component :: forall q o m. MonadAff m => H.Component q Input o m
component = H.mkComponent
  { initialState: \_ -> { installed: false }
  , render: \_ -> HH.text ""  -- Renders nothing
  , eval: H.mkEval $ H.defaultEval
      { initialize = Just Initialize
      , handleAction = handleAction
      }
  }

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Void m Unit
handleAction Initialize = do
  state <- H.get
  unless state.installed do
    liftEffect installFavicon
    H.modify_ _ { installed = true }

-- ═══════════════════════════════════════════════════════════════════════════════
-- FFI
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Install favicon links and meta tags into document head
-- | This is a legitimate DOM operation - modifying document.head
foreign import installFavicon :: Effect Unit
