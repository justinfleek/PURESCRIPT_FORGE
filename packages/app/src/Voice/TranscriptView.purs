-- | Voice transcript message display
-- | Migrated from opencode-dev/packages/app/src/components/voice/TranscriptView.tsx
module Opencode.App.Voice.TranscriptView
  ( TranscriptMessage
  , MessageRole(..)
  , Props
  , component
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Array (length, null)
import Data.DateTime (DateTime)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

data MessageRole = User | Assistant

derive instance eqMessageRole :: Eq MessageRole

type TranscriptMessage =
  { id :: String
  , role :: MessageRole
  , text :: String
  , timestamp :: DateTime
  , audioUrl :: Maybe String
  }

type Props =
  { messages :: Array TranscriptMessage
  }

component :: forall q o m. H.Component q Props o m
component = H.mkComponent
  { initialState: identity
  , render
  , eval: H.mkEval H.defaultEval
  }
  where
  render :: Props -> H.ComponentHTML () () m
  render props =
    HH.div
      [ HP.class_ (H.ClassName "flex flex-col gap-4 p-4 h-full overflow-y-auto") ]
      [ if null props.messages
          then renderEmpty
          else renderMessages props.messages
      ]

  renderEmpty :: H.ComponentHTML () () m
  renderEmpty =
    HH.div
      [ HP.class_ (H.ClassName "text-center text-muted-foreground py-8") ]
      [ HH.text "No messages yet. Start speaking to begin the conversation." ]

  renderMessages :: Array TranscriptMessage -> H.ComponentHTML () () m
  renderMessages messages =
    HH.div_ (map renderMessage messages)

  renderMessage :: TranscriptMessage -> H.ComponentHTML () () m
  renderMessage msg =
    HH.div
      [ HP.class_ (H.ClassName $ "flex gap-3 " <> alignment msg.role) ]
      [ HH.div
          [ HP.class_ (H.ClassName $ "max-w-[80%] rounded-lg p-3 " <> bubbleStyle msg.role) ]
          [ HH.div
              [ HP.class_ (H.ClassName "text-sm font-medium mb-1") ]
              [ HH.text (roleLabel msg.role) ]
          , HH.div
              [ HP.class_ (H.ClassName "text-sm whitespace-pre-wrap") ]
              [ HH.text msg.text ]
          , renderAudio msg.audioUrl
          ]
      ]

  alignment :: MessageRole -> String
  alignment User = "justify-end"
  alignment Assistant = "justify-start"

  bubbleStyle :: MessageRole -> String
  bubbleStyle User = "bg-primary text-primary-foreground"
  bubbleStyle Assistant = "bg-muted"

  roleLabel :: MessageRole -> String
  roleLabel User = "You"
  roleLabel Assistant = "Assistant"

  renderAudio :: Maybe String -> H.ComponentHTML () () m
  renderAudio Nothing = HH.text ""
  renderAudio (Just url) =
    HH.audio
      [ HP.src url
      , HP.attr (H.AttrName "controls") ""
      , HP.class_ (H.ClassName "mt-2 w-full")
      ]
      []
