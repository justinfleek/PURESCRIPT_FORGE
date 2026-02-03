-- | Logo Components
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/logo.tsx (60 lines)
-- |
-- | Forge brand logos in different variants.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | Mark:
-- | - `data-component="logo-mark"` - SVG element
-- | - `data-slot="logo-logo-mark-shadow"` - Shadow/inner path
-- | - `data-slot="logo-logo-mark-o"` - Main "O" path
-- |
-- | Splash:
-- | - `data-component="logo-splash"` - SVG element
-- |
-- | Logo:
-- | - Standard SVG wordmark
-- |
-- | CSS Custom Properties:
-- | - `--icon-weak-base` - Lighter/shadow color
-- | - `--icon-base` - Standard color
-- | - `--icon-strong-base` - Emphasized color
module UI.Components.Logo
  ( markComponent
  , splashComponent
  , logoComponent
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

-- | Logo input props
type Input =
  { className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { className: Nothing
  }

-- | Internal state
type State = { input :: Input }

-- | Internal actions
data Action = Receive Input

-- ═══════════════════════════════════════════════════════════════════════════════
-- MARK COMPONENT (O icon)
-- ═══════════════════════════════════════════════════════════════════════════════

markComponent :: forall q o m. MonadAff m => H.Component q Input o m
markComponent = H.mkComponent
  { initialState: \input -> { input }
  , render: renderMark
  , eval: H.mkEval $ H.defaultEval
      { receive = Just <<< Receive
      }
  }

renderMark :: forall m. State -> H.ComponentHTML Action () m
renderMark state =
  HH.element (HH.ElemName "svg")
    ([ HP.attr (HH.AttrName "data-component") "logo-mark"
     , HP.attr (HH.AttrName "viewBox") "0 0 16 20"
     , HP.attr (HH.AttrName "fill") "none"
     , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
     ] <> classAttr state.input.className)
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "data-slot") "logo-logo-mark-shadow"
        , HP.attr (HH.AttrName "d") "M12 16H4V8H12V16Z"
        , HP.attr (HH.AttrName "fill") "var(--icon-weak-base)"
        ] []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "data-slot") "logo-logo-mark-o"
        , HP.attr (HH.AttrName "d") "M12 4H4V16H12V4ZM16 20H0V0H16V20Z"
        , HP.attr (HH.AttrName "fill") "var(--icon-strong-base)"
        ] []
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- SPLASH COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

splashComponent :: forall q o m. MonadAff m => H.Component q Input o m
splashComponent = H.mkComponent
  { initialState: \input -> { input }
  , render: renderSplash
  , eval: H.mkEval $ H.defaultEval
      { receive = Just <<< Receive
      }
  }

renderSplash :: forall m. State -> H.ComponentHTML Action () m
renderSplash state =
  HH.element (HH.ElemName "svg")
    ([ HP.attr (HH.AttrName "data-component") "logo-splash"
     , HP.attr (HH.AttrName "viewBox") "0 0 80 100"
     , HP.attr (HH.AttrName "fill") "none"
     , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
     ] <> classAttr state.input.className)
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M60 80H20V40H60V80Z"
        , HP.attr (HH.AttrName "fill") "var(--icon-base)"
        ] []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M60 20H20V80H60V20ZM80 100H0V0H80V100Z"
        , HP.attr (HH.AttrName "fill") "var(--icon-strong-base)"
        ] []
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- LOGO COMPONENT (Full wordmark)
-- ═══════════════════════════════════════════════════════════════════════════════

logoComponent :: forall q o m. MonadAff m => H.Component q Input o m
logoComponent = H.mkComponent
  { initialState: \input -> { input }
  , render: renderLogo
  , eval: H.mkEval $ H.defaultEval
      { receive = Just <<< Receive
      }
  }

renderLogo :: forall m. State -> H.ComponentHTML Action () m
renderLogo state =
  HH.element (HH.ElemName "svg")
    ([ HP.attr (HH.AttrName "viewBox") "0 0 234 42"
     , HP.attr (HH.AttrName "fill") "none"
     , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
     ] <> classAttr state.input.className)
    [ HH.element (HH.ElemName "g") []
        -- O
        [ renderPath "M18 30H6V18H18V30Z" "--icon-weak-base"
        , renderPath "M18 12H6V30H18V12ZM24 36H0V6H24V36Z" "--icon-base"
        -- P
        , renderPath "M48 30H36V18H48V30Z" "--icon-weak-base"
        , renderPath "M36 30H48V12H36V30ZM54 36H36V42H30V6H54V36Z" "--icon-base"
        -- E
        , renderPath "M84 24V30H66V24H84Z" "--icon-weak-base"
        , renderPath "M84 24H66V30H84V36H60V6H84V24ZM66 18H78V12H66V18Z" "--icon-base"
        -- N
        , renderPath "M108 36H96V18H108V36Z" "--icon-weak-base"
        , renderPath "M108 12H96V36H90V6H108V12ZM114 36H108V12H114V36Z" "--icon-base"
        -- C
        , renderPath "M144 30H126V18H144V30Z" "--icon-weak-base"
        , renderPath "M144 12H126V30H144V36H120V6H144V12Z" "--icon-strong-base"
        -- O
        , renderPath "M168 30H156V18H168V30Z" "--icon-weak-base"
        , renderPath "M168 12H156V30H168V12ZM174 36H150V6H174V36Z" "--icon-strong-base"
        -- D
        , renderPath "M198 30H186V18H198V30Z" "--icon-weak-base"
        , renderPath "M198 12H186V30H198V12ZM204 36H180V6H198V0H204V36Z" "--icon-strong-base"
        -- E
        , renderPath "M234 24V30H216V24H234Z" "--icon-weak-base"
        , renderPath "M216 12V18H228V12H216ZM234 24H216V30H234V36H210V6H234V24Z" "--icon-strong-base"
        ]
    ]

renderPath :: forall w i. String -> String -> HH.HTML w i
renderPath d colorVar =
  HH.element (HH.ElemName "path")
    [ HP.attr (HH.AttrName "d") d
    , HP.attr (HH.AttrName "fill") ("var(" <> colorVar <> ")")
    ] []

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- These components render static SVG paths.
