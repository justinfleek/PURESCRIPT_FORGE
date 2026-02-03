-- | Microphone toggle button with audio level indicator
-- | Migrated from forge-dev/packages/app/src/components/voice/MicrophoneButton.tsx
module Forge.App.Voice.MicrophoneButton
  ( Props
  , Output(..)
  , component
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE

type Props =
  { isListening :: Boolean
  , isProcessing :: Boolean
  , audioLevel :: Maybe Number  -- 0-1 for visualization
  , disabled :: Boolean
  }

data Output
  = Start
  | Stop

component :: forall q m. H.Component q Props Output m
component = H.mkComponent
  { initialState: identity
  , render
  , eval: H.mkEval H.defaultEval { handleAction = handleAction }
  }
  where
  render :: Props -> H.ComponentHTML Output () m
  render props =
    HH.button
      [ HP.class_ (H.ClassName $ "relative " <> buttonVariant props.isListening)
      , HP.disabled (props.disabled || props.isProcessing)
      , HE.onClick \_ -> if props.isListening then Stop else Start
      ]
      [ renderIcon props.isListening
      , renderPulse props
      ]

  renderIcon :: Boolean -> H.ComponentHTML Output () m
  renderIcon isListening =
    HH.span
      [ HP.class_ (H.ClassName "icon") ]
      [ HH.text (if isListening then "mic-off" else "mic") ]

  renderPulse :: Props -> H.ComponentHTML Output () m
  renderPulse props =
    case props.audioLevel of
      Just level | props.isListening && level > 0.0 ->
        HH.div
          [ HP.class_ (H.ClassName "absolute inset-0 rounded-full bg-red-500/20 animate-pulse")
          , HP.style $ "transform: scale(" <> show (1.0 + level * 0.5) <> "); transition: transform 0.1s"
          ]
          []
      _ -> HH.text ""

  buttonVariant :: Boolean -> String
  buttonVariant true = "btn-primary btn-large"
  buttonVariant false = "btn-secondary btn-large"

  handleAction :: Output -> H.HalogenM Props Output () Output m Unit
  handleAction = H.raise
