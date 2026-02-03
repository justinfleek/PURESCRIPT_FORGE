-- | ProgressCircle Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/progress-circle.tsx (58 lines)
-- |
-- | Circular progress indicator with percentage display.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-component="progress-circle"` - SVG element
-- | - `data-slot="progress-circle-background"` - Background track circle
-- | - `data-slot="progress-circle-progress"` - Progress arc circle
module UI.Components.ProgressCircle
  ( component
  , Input
  , defaultInput
  ) where

import Prelude

import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Math (pi)

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | ProgressCircle input props
type Input =
  { percentage :: Number      -- 0.0 to 100.0
  , size :: Int               -- SVG width/height in pixels
  , strokeWidth :: Int        -- Stroke width in SVG units
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { percentage: 0.0
  , size: 16
  , strokeWidth: 3
  , className: Nothing
  }

-- | Internal state
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
  let viewBoxSize = 16.0
      center = viewBoxSize / 2.0
      radius = center - toNumber state.input.strokeWidth / 2.0
      circumference = 2.0 * pi * radius
      clampedPercent = clamp 0.0 100.0 state.input.percentage
      progress = clampedPercent / 100.0
      offset = circumference * (1.0 - progress)
  in
    HH.element (HH.ElemName "svg")
      ([ HP.attr (HH.AttrName "data-component") "progress-circle"
       , HP.attr (HH.AttrName "width") (show state.input.size)
       , HP.attr (HH.AttrName "height") (show state.input.size)
       , HP.attr (HH.AttrName "viewBox") "0 0 16 16"
       , HP.attr (HH.AttrName "fill") "none"
       ] <> classAttr state.input.className)
      [ -- Background circle
        HH.element (HH.ElemName "circle")
          [ HP.attr (HH.AttrName "cx") (show center)
          , HP.attr (HH.AttrName "cy") (show center)
          , HP.attr (HH.AttrName "r") (show radius)
          , HP.attr (HH.AttrName "data-slot") "progress-circle-background"
          , HP.attr (HH.AttrName "stroke-width") (show state.input.strokeWidth)
          ] []
      , -- Progress circle
        HH.element (HH.ElemName "circle")
          [ HP.attr (HH.AttrName "cx") (show center)
          , HP.attr (HH.AttrName "cy") (show center)
          , HP.attr (HH.AttrName "r") (show radius)
          , HP.attr (HH.AttrName "data-slot") "progress-circle-progress"
          , HP.attr (HH.AttrName "stroke-width") (show state.input.strokeWidth)
          , HP.attr (HH.AttrName "stroke-dasharray") (show circumference)
          , HP.attr (HH.AttrName "stroke-dashoffset") (show offset)
          , HP.attr (HH.AttrName "transform") "rotate(-90 8 8)"  -- Start from top
          ] []
      ]

-- | Clamp a value to a range
clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal val
  | val < minVal = minVal
  | val > maxVal = maxVal
  | otherwise = val

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs and Math.pi.
