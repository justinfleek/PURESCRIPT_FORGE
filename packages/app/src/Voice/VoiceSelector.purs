-- | Voice selection dropdown
-- | Migrated from forge-dev/packages/app/src/components/voice/VoiceSelector.tsx
module Forge.App.Voice.VoiceSelector
  ( Props
  , Output(..)
  , component
  ) where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Halogen.Hooks as Hooks

type Props =
  { voices :: Array String
  , selectedVoice :: String
  , disabled :: Boolean
  }

data Output = VoiceChanged String

data Action
  = Toggle
  | SelectVoice String

component :: forall q m. H.Component q Props Output m
component = Hooks.component \{ props, outputToken } -> Hooks.do
  isOpen /\ isOpenId <- Hooks.useState false
  
  let
    handleToggle = Hooks.modify_ isOpenId not
    
    handleSelect voice = do
      Hooks.put isOpenId false
      Hooks.raise outputToken (VoiceChanged voice)

  Hooks.pure do
    HH.div
      [ HP.class_ (H.ClassName "relative") ]
      [ renderButton props isOpen handleToggle
      , renderDropdown props isOpen handleSelect
      ]

  where
  renderButton props isOpen onToggle =
    HH.button
      [ HP.class_ (H.ClassName "btn btn-secondary btn-small")
      , HP.disabled props.disabled
      , HE.onClick \_ -> onToggle
      ]
      [ HH.span [ HP.class_ (H.ClassName "icon mr-2") ] [ HH.text "user" ]
      , HH.text props.selectedVoice
      , HH.span [ HP.class_ (H.ClassName "icon ml-2") ] [ HH.text "chevron-down" ]
      ]

  renderDropdown props isOpen onSelect =
    if isOpen
      then
        HH.div
          [ HP.class_ (H.ClassName "absolute top-full mt-2 bg-background border rounded-lg shadow-lg z-50 min-w-[200px]") ]
          (map (renderVoiceOption props.selectedVoice onSelect) props.voices)
      else HH.text ""

  renderVoiceOption selectedVoice onSelect voice =
    HH.button
      [ HP.class_ (H.ClassName $ "w-full text-left px-4 py-2 hover:bg-muted " <> 
          if voice == selectedVoice then "bg-primary/10" else "")
      , HE.onClick \_ -> onSelect voice
      ]
      [ HH.text voice ]
