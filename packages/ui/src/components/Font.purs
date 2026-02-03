-- | Font Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/font.tsx (167 lines)
-- |
-- | Injects font face definitions and preload links into document head.
-- | This is a side-effect component that adds @font-face CSS on initialization.
-- |
-- | Primary fonts:
-- | - Inter: Sans-serif variable font (100-900 weights)
-- | - IBM Plex Mono: Monospace (400, 500, 700 weights)
-- |
-- | Nerd Font variants available for code display.
module UI.Components.Font
  ( component
  , installFonts
  , MonoFont
  , monoNerdFonts
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Monospace font definition
type MonoFont =
  { family :: String
  , regular :: String
  , bold :: String
  }

-- No input needed
type Input = Unit

-- | Internal state
type State = { installed :: Boolean }

-- | Internal actions
data Action = Initialize

-- ═══════════════════════════════════════════════════════════════════════════════
-- AVAILABLE NERD FONTS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | List of available monospace Nerd Fonts
monoNerdFonts :: Array MonoFont
monoNerdFonts =
  [ { family: "JetBrains Mono Nerd Font"
    , regular: "/fonts/jetbrains-mono-nerd-font.woff2"
    , bold: "/fonts/jetbrains-mono-nerd-font-bold.woff2"
    }
  , { family: "Fira Code Nerd Font"
    , regular: "/fonts/fira-code-nerd-font.woff2"
    , bold: "/fonts/fira-code-nerd-font-bold.woff2"
    }
  , { family: "Cascadia Code Nerd Font"
    , regular: "/fonts/cascadia-code-nerd-font.woff2"
    , bold: "/fonts/cascadia-code-nerd-font-bold.woff2"
    }
  , { family: "Hack Nerd Font"
    , regular: "/fonts/hack-nerd-font.woff2"
    , bold: "/fonts/hack-nerd-font-bold.woff2"
    }
  , { family: "Source Code Pro Nerd Font"
    , regular: "/fonts/source-code-pro-nerd-font.woff2"
    , bold: "/fonts/source-code-pro-nerd-font-bold.woff2"
    }
  , { family: "Inconsolata Nerd Font"
    , regular: "/fonts/inconsolata-nerd-font.woff2"
    , bold: "/fonts/inconsolata-nerd-font-bold.woff2"
    }
  , { family: "Roboto Mono Nerd Font"
    , regular: "/fonts/roboto-mono-nerd-font.woff2"
    , bold: "/fonts/roboto-mono-nerd-font-bold.woff2"
    }
  , { family: "Ubuntu Mono Nerd Font"
    , regular: "/fonts/ubuntu-mono-nerd-font.woff2"
    , bold: "/fonts/ubuntu-mono-nerd-font-bold.woff2"
    }
  , { family: "Intel One Mono Nerd Font"
    , regular: "/fonts/intel-one-mono-nerd-font.woff2"
    , bold: "/fonts/intel-one-mono-nerd-font-bold.woff2"
    }
  , { family: "Meslo LGS Nerd Font"
    , regular: "/fonts/meslo-lgs-nerd-font.woff2"
    , bold: "/fonts/meslo-lgs-nerd-font-bold.woff2"
    }
  , { family: "Iosevka Nerd Font"
    , regular: "/fonts/iosevka-nerd-font.woff2"
    , bold: "/fonts/iosevka-nerd-font-bold.woff2"
    }
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Halogen component that installs fonts on mount
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
    liftEffect installFonts
    H.modify_ _ { installed = true }

-- ═══════════════════════════════════════════════════════════════════════════════
-- FFI
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Install font face definitions and preload links into document head
-- | This is a legitimate DOM operation - modifying document.head
foreign import installFonts :: Effect Unit
