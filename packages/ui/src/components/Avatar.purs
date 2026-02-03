-- | Avatar Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/avatar.tsx (45 lines)
-- |
-- | User avatar with image support and fallback initials.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-component="avatar"` - Root element
-- | - `data-size="small|normal|large"` - Size variant
-- | - `data-has-image` - Present when displaying image
-- | - `data-slot="avatar-image"` - Image element
-- |
-- | CSS Custom Properties:
-- | - `--avatar-bg` - Background color (when no image)
-- | - `--avatar-fg` - Foreground/text color (when no image)
module UI.Components.Avatar
  ( component
  , Input
  , AvatarSize(..)
  , defaultInput
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String (take)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Avatar size variants
data AvatarSize
  = Small
  | Normal
  | Large

derive instance eqAvatarSize :: Eq AvatarSize

sizeToString :: AvatarSize -> String
sizeToString Small = "small"
sizeToString Normal = "normal"
sizeToString Large = "large"

-- | Avatar input props
type Input =
  { fallback :: String           -- Fallback text (first char used)
  , src :: Maybe String          -- Image URL
  , background :: Maybe String   -- Custom background color
  , foreground :: Maybe String   -- Custom foreground color
  , size :: AvatarSize
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { fallback: "?"
  , src: Nothing
  , background: Nothing
  , foreground: Nothing
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
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "avatar"
     , HP.attr (HH.AttrName "data-size") (sizeToString state.input.size)
     ] <> hasImageAttr state.input.src
       <> styleAttr state.input
       <> classAttr state.input.className)
    [ renderContent state ]

renderContent :: forall m. State -> H.ComponentHTML Action () m
renderContent state =
  case state.input.src of
    Just url ->
      HH.img
        [ HP.src url
        , HP.attr (HH.AttrName "data-slot") "avatar-image"
        , HP.attr (HH.AttrName "draggable") "false"
        , HP.attr (HH.AttrName "alt") ""
        ]
    Nothing ->
      HH.text (take 1 state.input.fallback)

-- Helper for data-has-image attribute
hasImageAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
hasImageAttr (Just _) = [ HP.attr (HH.AttrName "data-has-image") "" ]
hasImageAttr Nothing = []

-- Helper for custom CSS properties
styleAttr :: forall r i. Input -> Array (HP.IProp r i)
styleAttr input =
  case input.src of
    Just _ -> []  -- No custom colors when image is present
    Nothing ->
      let bgStyle = case input.background of
            Just bg -> "--avatar-bg: " <> bg <> "; "
            Nothing -> ""
          fgStyle = case input.foreground of
            Just fg -> "--avatar-fg: " <> fg <> "; "
            Nothing -> ""
          combined = bgStyle <> fgStyle
      in if combined == ""
         then []
         else [ HP.attr (HH.AttrName "style") combined ]

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs.
