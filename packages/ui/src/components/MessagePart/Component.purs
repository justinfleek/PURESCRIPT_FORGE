-- | MessagePart Component Module
-- | Main message and part rendering components.
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/message-part.tsx
-- | This module contains the Message and Part components.

module UI.Components.MessagePart.Component
  ( messageComponent
  , partComponent
  , userMessageComponent
  , assistantMessageComponent
  , Query(..)
  , Input
  , Output(..)
  , Slot
  ) where

import Prelude

import Data.Array (filter, find)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import UI.Components.MessagePart.Types (Message, Part(..), MessageProps, MessagePartProps, TextPartData, FilePartData, AgentPartData, partType)

-- ═══════════════════════════════════════════════════════════════════════════════
-- MESSAGE COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

type Input = MessageProps

data Output
  = CopyClicked String
  | ExpandToggled Boolean

data Query a
  = GetMessage (Message -> a)

type State =
  { input :: Input
  , expanded :: Boolean
  , copied :: Boolean
  }

data Action
  = Initialize
  | Receive Input
  | HandleCopy String
  | HandleExpandToggle

type Slot id = H.Slot Query Output id

messageComponent :: forall m. MonadAff m => H.Component Query Input Output m
messageComponent = H.mkComponent
  { initialState
  , render: renderMessage
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleMessageAction
      , handleQuery = handleMessageQuery
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { input
  , expanded: false
  , copied: false
  }

renderMessage :: forall m. State -> H.ComponentHTML Action () m
renderMessage state =
  case state.input.message.role of
    "user" -> renderUserMessage state
    "assistant" -> renderAssistantMessage state
    _ -> HH.text ""

renderUserMessage :: forall m. State -> H.ComponentHTML Action () m
renderUserMessage state =
  HH.div
    [ HP.attr (HH.AttrName "data-component") "user-message"
    , HP.attr (HH.AttrName "data-expanded") (show state.expanded)
    ]
    [ renderAttachments state
    , renderUserText state
    ]

renderAttachments :: forall m. State -> H.ComponentHTML Action () m
renderAttachments state =
  let attachments = filter isAttachment state.input.parts
  in if length attachments == 0
     then HH.text ""
     else HH.div
       [ HP.attr (HH.AttrName "data-slot") "user-message-attachments" ]
       (map renderAttachment attachments)
  where
    length = Data.Array.length

renderAttachment :: forall m. Part -> H.ComponentHTML Action () m
renderAttachment (FilePart fp) =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "user-message-attachment"
    , HP.attr (HH.AttrName "data-type") (if isImage fp.mime then "image" else "file")
    ]
    [ case fp.url of
        Just url | isImage fp.mime ->
          HH.img
            [ HP.src url
            , HP.alt (fromMaybe "Attachment" fp.filename)
            , HP.attr (HH.AttrName "data-slot") "user-message-attachment-image"
            ]
        _ ->
          HH.div
            [ HP.attr (HH.AttrName "data-slot") "user-message-attachment-icon" ]
            [ HH.text "📁" ]
    ]
renderAttachment _ = HH.text ""

renderUserText :: forall m. State -> H.ComponentHTML Action () m
renderUserText state =
  case findTextPart state.input.parts of
    Nothing -> HH.text ""
    Just textPart ->
      HH.div
        [ HP.attr (HH.AttrName "data-slot") "user-message-text"
        , HE.onClick \_ -> HandleExpandToggle
        ]
        [ HH.text textPart.text
        , renderCopyButton textPart.text
        ]

renderCopyButton :: forall m. String -> H.ComponentHTML Action () m
renderCopyButton content =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "user-message-copy-wrapper" ]
    [ HH.button
        [ HP.type_ HP.ButtonButton
        , HE.onClick \_ -> HandleCopy content
        ]
        [ HH.text "Copy" ]
    ]

renderAssistantMessage :: forall m. State -> H.ComponentHTML Action () m
renderAssistantMessage state =
  let filteredParts = filter (not <<< isTodoRead) state.input.parts
  in HH.div
       [ HP.attr (HH.AttrName "data-component") "assistant-message" ]
       (map renderPart filteredParts)

renderPart :: forall m. Part -> H.ComponentHTML Action () m
renderPart part =
  HH.div
    [ HP.attr (HH.AttrName "data-part-type") (partType part) ]
    [ HH.text (partType part <> " part") ]

-- Helpers
isAttachment :: Part -> Boolean
isAttachment (FilePart fp) = isImage fp.mime || fp.mime == "application/pdf"
isAttachment _ = false

isImage :: String -> Boolean
isImage mime = startsWith "image/" mime

isTodoRead :: Part -> Boolean
isTodoRead (ToolPart tp) = tp.tool == "todoread"
isTodoRead _ = false

findTextPart :: Array Part -> Maybe TextPartData
findTextPart parts = go parts
  where
    go [] = Nothing
    go (TextPart tp : _) | not tp.synthetic = Just tp
    go (_ : rest) = go rest

foreign import startsWith :: String -> String -> Boolean

handleMessageAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleMessageAction = case _ of
  Initialize -> pure unit
  
  Receive newInput -> 
    H.modify_ _ { input = newInput }
  
  HandleCopy content -> do
    liftEffect $ copyToClipboard content
    H.modify_ _ { copied = true }
    -- Reset after 2 seconds would need a timer
    H.raise (CopyClicked content)
  
  HandleExpandToggle -> do
    state <- H.get
    H.modify_ _ { expanded = not state.expanded }
    H.raise (ExpandToggled (not state.expanded))

handleMessageQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleMessageQuery = case _ of
  GetMessage reply -> do
    state <- H.get
    pure (Just (reply state.input.message))

foreign import copyToClipboard :: String -> Effect Unit

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

type PartInput = MessagePartProps

partComponent :: forall m. MonadAff m => H.Component Query PartInput Output m
partComponent = H.mkComponent
  { initialState: \input -> { input, expanded: false, copied: false }
  , render: \state -> renderPartDisplay state.input.part
  , eval: H.mkEval H.defaultEval
  }

renderPartDisplay :: forall m. Part -> H.ComponentHTML Action () m
renderPartDisplay (TextPart tp) =
  HH.div
    [ HP.attr (HH.AttrName "data-component") "text-part" ]
    [ HH.div
        [ HP.attr (HH.AttrName "data-slot") "text-part-body" ]
        [ HH.text tp.text ]
    ]

renderPartDisplay (ReasoningPart rp) =
  HH.div
    [ HP.attr (HH.AttrName "data-component") "reasoning-part" ]
    [ HH.text rp.text ]

renderPartDisplay (ToolPart tp) =
  HH.div
    [ HP.attr (HH.AttrName "data-component") "tool-part-wrapper" ]
    [ HH.text ("Tool: " <> tp.tool) ]

renderPartDisplay (FilePart fp) =
  HH.div
    [ HP.attr (HH.AttrName "data-component") "file-part" ]
    [ HH.text (fromMaybe "File" fp.filename) ]

renderPartDisplay (AgentPart _) =
  HH.div
    [ HP.attr (HH.AttrName "data-component") "agent-part" ]
    [ HH.text "Agent" ]

-- Aliases for specific message types
userMessageComponent :: forall m. MonadAff m => H.Component Query Input Output m
userMessageComponent = messageComponent

assistantMessageComponent :: forall m. MonadAff m => H.Component Query Input Output m
assistantMessageComponent = messageComponent
