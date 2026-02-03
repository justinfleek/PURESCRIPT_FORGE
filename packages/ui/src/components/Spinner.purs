-- | Spinner Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/spinner.tsx (52 lines)
-- |
-- | Animated loading spinner with 4x4 grid of squares.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | The spinner is a 4x4 grid (16 squares) with:
-- | - Corner squares (0, 3, 12, 15) are hidden
-- | - Outer squares (1, 2, 4, 7, 8, 11, 13, 14) use dim pulse
-- | - Inner squares (5, 6, 9, 10) use normal pulse
-- |
-- | Data Attributes:
-- | - `data-component="spinner"` - The SVG element
module UI.Components.Spinner
  ( component
  , Input
  , defaultInput
  ) where

import Prelude

import Data.Array (mapWithIndex)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Spinner input props
type Input =
  { className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { className: Nothing
  }

-- | Internal state (stateless component)
type State = { input :: Input }

-- | Internal actions
data Action = Receive Input

-- | Square configuration for the 4x4 grid
type SquareConfig =
  { id :: Int
  , x :: Int
  , y :: Int
  , delay :: Number
  , duration :: Number
  , isOuter :: Boolean
  , isCorner :: Boolean
  }

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
  HH.element (HH.ElemName "svg")
    ([ HP.attr (HH.AttrName "data-component") "spinner"
    , HP.attr (HH.AttrName "viewBox") "0 0 15 15"
    , HP.attr (HH.AttrName "fill") "currentColor"
    , HP.attr (HH.AttrName "aria-hidden") "true"
    , HP.attr (HH.AttrName "role") "status"
    ] <> classAttr state.input.className)
    (map renderSquare squares)

-- | Render a single square in the spinner grid
renderSquare :: forall w i. SquareConfig -> HH.HTML w i
renderSquare sq =
  HH.element (HH.ElemName "rect")
    [ HP.attr (HH.AttrName "x") (show sq.x)
    , HP.attr (HH.AttrName "y") (show sq.y)
    , HP.attr (HH.AttrName "width") "3"
    , HP.attr (HH.AttrName "height") "3"
    , HP.attr (HH.AttrName "rx") "1"
    , HP.attr (HH.AttrName "style") (squareStyle sq)
    ]
    []

-- | Generate CSS style for a square
squareStyle :: SquareConfig -> String
squareStyle sq
  | sq.isCorner = "opacity: 0;"
  | otherwise =
      let animName = if sq.isOuter then "pulse-opacity-dim" else "pulse-opacity"
      in "animation: " <> animName <> " " <> show sq.duration <> "s ease-in-out infinite; " <>
         "animation-delay: " <> show sq.delay <> "s;"

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- SQUARE CONFIGURATION (Deterministic)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set of outer square indices (not corners, not inner)
isOuterIndex :: Int -> Boolean
isOuterIndex i = i == 1 || i == 2 || i == 4 || i == 7 || i == 8 || i == 11 || i == 13 || i == 14

-- | Set of corner square indices (hidden)
isCornerIndex :: Int -> Boolean
isCornerIndex i = i == 0 || i == 3 || i == 12 || i == 15

-- | Generate deterministic pseudo-random delay based on index
-- | Uses a simple LCG-like formula for reproducible "random" values
-- | This maintains the organic feel while being fully deterministic
pseudoRandomDelay :: Int -> Number
pseudoRandomDelay i = 
  let -- Use index-based deterministic values that look random
      seed = (i * 1103515245 + 12345) `mod` 2147483648
      normalized = toNumber seed / 2147483648.0
  in normalized * 1.5  -- Scale to 0-1.5 seconds

-- | Generate deterministic pseudo-random duration based on index
pseudoRandomDuration :: Int -> Number
pseudoRandomDuration i =
  let seed = ((i + 7) * 1103515245 + 12345) `mod` 2147483648
      normalized = toNumber seed / 2147483648.0
  in 1.0 + normalized  -- Scale to 1-2 seconds

-- | Pre-computed square configurations (deterministic)
squares :: Array SquareConfig
squares = mapWithIndex mkSquare (0..15)
  where
    mkSquare :: Int -> Int -> SquareConfig
    mkSquare _ i =
      { id: i
      , x: (i `mod` 4) * 4
      , y: (i / 4) * 4
      , delay: pseudoRandomDelay i
      , duration: pseudoRandomDuration i
      , isOuter: isOuterIndex i
      , isCorner: isCornerIndex i
      }

-- | Range helper (PureScript doesn't have .. built in)
infix 8 range as ..

range :: Int -> Int -> Array Int
range start end
  | start > end = []
  | otherwise = go start []
  where
    go n acc
      | n > end = acc
      | otherwise = go (n + 1) (acc <> [n])

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs.
-- SVG is rendered as pure Halogen HTML.
-- Animation is handled by CSS keyframes (pulse-opacity, pulse-opacity-dim).
