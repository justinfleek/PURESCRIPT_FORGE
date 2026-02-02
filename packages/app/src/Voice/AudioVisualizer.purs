-- | Audio level visualizer component
-- | Migrated from opencode-dev/packages/app/src/components/voice/AudioVisualizer.tsx
module Opencode.App.Voice.AudioVisualizer
  ( Props
  , component
  ) where

import Prelude
import Effect (Effect)
import Effect.Ref (Ref, new, read, write)
import Data.Maybe (Maybe(..))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.Hooks as Hooks
import Web.HTML.Window (requestAnimationFrame, cancelAnimationFrame)

type Props =
  { audioLevel :: Number  -- 0-1
  , isActive :: Boolean
  }

type State =
  { displayLevel :: Number
  , animationFrameId :: Maybe Int
  }

component :: forall q o m. H.Component q Props o m
component = Hooks.component \{ props } -> Hooks.do
  state /\ stateId <- Hooks.useState { displayLevel: 0.0, animationFrameId: Nothing }
  
  -- Effect to handle animation
  Hooks.useLifecycleEffect do
    when props.isActive do
      startAnimation stateId props.audioLevel
    pure $ Just do
      st <- Hooks.get stateId
      case st.animationFrameId of
        Just id -> cancelAnimationFrame id
        Nothing -> pure unit

  Hooks.pure do
    let size = 32.0 + state.displayLevel * 64.0
    let opacity = if props.isActive then 0.6 + state.displayLevel * 0.4 else 0.2
    HH.div
      [ HP.class_ (H.ClassName "flex items-center justify-center w-32 h-32") ]
      [ HH.div
          [ HP.class_ (H.ClassName "rounded-full bg-gradient-to-r from-blue-500 to-purple-500 transition-all duration-100")
          , HP.style $ "width: " <> show size <> "px; height: " <> show size <> "px; opacity: " <> show opacity
          ]
          []
      ]

-- Animation loop (simplified - actual implementation needs FFI)
startAnimation :: forall m. Hooks.StateId State -> Number -> Hooks.HookM m Unit
startAnimation stateId targetLevel = do
  st <- Hooks.get stateId
  let newLevel = st.displayLevel + (targetLevel - st.displayLevel) * 0.3
  Hooks.put stateId (st { displayLevel = newLevel })
