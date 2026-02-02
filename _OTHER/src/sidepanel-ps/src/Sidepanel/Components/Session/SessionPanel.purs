-- | Session Panel Component - Chat Session Detail View
-- |
-- | **What:** Displays detailed information about the current chat session, including
-- |         message history, token usage, costs, and tool calls. Supports session
-- |         export and clearing.
-- | **Why:** Provides users with comprehensive session details for analysis, debugging,
-- |         and record-keeping. Enables export for backup or sharing.
-- | **How:** Renders session information, message list with expandable messages, tool
-- |         call status, and provides export functionality (JSON and Markdown formats).
-- |         Updates duration display every second via background timer.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.AppState`: Session state types
-- | - `Sidepanel.Utils.Currency`: Currency formatting
-- | - `Sidepanel.Utils.Time`: Time formatting
-- | - `Sidepanel.FFI.Download`: File download functionality
-- |
-- | **Mathematical Foundation:**
-- | - **Duration Calculation:** Duration is calculated as the difference between
-- |   `session.startedAt` and current time, updated every second.
-- | - **Message Expansion:** Messages can be expanded/collapsed individually, tracked
-- |   in `expandedMessages` Set.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Session.SessionPanel as SessionPanel
-- |
-- | -- In parent component:
-- | HH.slot _session unit SessionPanel.component sessionData
-- |   (case _ of
-- |     SessionPanel.SessionCleared -> HandleSessionCleared
-- |     SessionPanel.SessionExported id -> HandleSessionExported id)
-- | ```
-- |
-- | Based on spec 54-SESSION-PANEL.md
module Sidepanel.Components.Session.SessionPanel where

import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.DateTime (DateTime)
import Data.Set as Set
import Data.String as String
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Effect.Aff (Aff, delay, Milliseconds(..))
import Effect.Aff as Aff
import Sidepanel.State.AppState (SessionState)
import Sidepanel.Utils.Currency (formatUSD, formatNumber)
import Sidepanel.Utils.Time (formatTime, formatDuration)
import Sidepanel.FFI.DateTime (getCurrentDateTime, toISOString)
import Argonaut.Core (Json)
import Argonaut.Encode (class EncodeJson, encodeJson, (:=))
import Argonaut.Decode (class DecodeJson, decodeJson, (.:), (.:?))
import Sidepanel.FFI.Download (downloadFile)

-- | Extended session data with messages
type Session =
  { id :: String
  , model :: String
  , provider :: String
  , startedAt :: DateTime
  , promptTokens :: Int
  , completionTokens :: Int
  , cost :: Number
  , messages :: Array Message
  }

-- | Message with optional tool calls
type Message =
  { id :: String
  , role :: Role
  , content :: String
  , timestamp :: DateTime
  , usage :: Maybe MessageUsage
  , toolCalls :: Array ToolCall
  }

data Role = User | Assistant | System | Tool

derive instance eqRole :: Eq Role

type MessageUsage =
  { promptTokens :: Int
  , completionTokens :: Int
  , cost :: Number
  }

type ToolCall =
  { name :: String
  , status :: ToolStatus
  , durationMs :: Maybe Int
  }

data ToolStatus = Pending | Running | Completed | Failed

derive instance eqToolStatus :: Eq ToolStatus

-- | Component state
type State =
  { session :: Maybe Session
  , expandedMessages :: Set.Set String
  , isExporting :: Boolean
  , currentTime :: Maybe DateTime  -- For duration calculation
  }

-- | Actions
data Action
  = Receive (Maybe Session)
  | ToggleMessageExpand String
  | ExportSession
  | ClearSession
  | UpdateCurrentTime DateTime
  | Initialize

-- | Outputs
data Output
  = SessionCleared
  | SessionExported String

-- | Component input
type Input = Maybe Session

-- | Component
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      { session: input
      , expandedMessages: Set.empty
      , isExporting: false
      , currentTime: Nothing
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      , initialize = Just Initialize
      }
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state = case state.session of
  Nothing -> renderEmptyState
  Just session -> renderSession session state

renderEmptyState :: forall m. H.ComponentHTML Action () m
renderEmptyState =
  HH.div
    [ HP.classes [ H.ClassName "session-panel", H.ClassName "session-panel--empty" ] ]
    [ HH.div
        [ HP.class_ (H.ClassName "empty-state") ]
        [ HH.span [ HP.class_ (H.ClassName "empty-state__icon") ] [ HH.text "💬" ]
        , HH.p_ [ HH.text "No active session" ]
        , HH.p
            [ HP.class_ (H.ClassName "empty-state__hint") ]
            [ HH.text "Start a conversation in OpenCode to see details here" ]
        ]
    ]

renderSession :: forall m. Session -> State -> H.ComponentHTML Action () m
renderSession session state =
  HH.div
    [ HP.class_ (H.ClassName "session-panel") ]
    [ renderHeader state.isExporting
    , renderSessionInfo session
    , HH.div
        [ HP.class_ (H.ClassName "session-panel__messages") ]
        [ HH.div [ HP.class_ (H.ClassName "section-title") ] [ HH.text "Message History" ]
        , HH.div
            [ HP.class_ (H.ClassName "message-list") ]
            (map (renderMessage state.expandedMessages) session.messages)
        ]
    ]

renderHeader :: forall m. Boolean -> H.ComponentHTML Action () m
renderHeader isExporting =
  HH.header
    [ HP.class_ (H.ClassName "session-panel__header") ]
    [ HH.h2_ [ HH.text "Session Details" ]
    , HH.div
        [ HP.class_ (H.ClassName "session-panel__actions") ]
        [ HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--secondary" ]
            , HP.disabled isExporting
            , HE.onClick \_ -> ExportSession
            ]
            [ HH.text $ if isExporting then "Exporting..." else "Export" ]
        , HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--ghost" ]
            , HE.onClick \_ -> ClearSession
            ]
            [ HH.text "Clear" ]
        ]
    ]

renderSessionInfo :: forall m. Session -> H.ComponentHTML Action () m
renderSessionInfo session =
  HH.div
    [ HP.class_ (H.ClassName "session-info") ]
    [ HH.div
        [ HP.class_ (H.ClassName "session-info__header") ]
        [ HH.span [ HP.class_ (H.ClassName "session-info__title") ]
            [ HH.text "Current Session" ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "session-info__details") ]
        [ renderDetail "Model" session.model
        , renderDetail "Provider" session.provider
        , renderDetail "Started" (formatTime session.startedAt)
        , renderDetail "Duration" (formatSessionDuration session.startedAt state.currentTime)
        ]
    , HH.div
        [ HP.class_ (H.ClassName "session-info__metrics") ]
        [ renderMetric (formatNumber (toNumber session.promptTokens)) "Prompt"
        , renderMetric (formatNumber (toNumber session.completionTokens)) "Completion"
        , renderMetric (formatUSD session.cost) "Cost"
        ]
    ]

renderDetail :: forall m. String -> String -> H.ComponentHTML Action () m
renderDetail label value =
  HH.div
    [ HP.class_ (H.ClassName "session-detail") ]
    [ HH.span [ HP.class_ (H.ClassName "session-detail__label") ] [ HH.text label ]
    , HH.span [ HP.class_ (H.ClassName "session-detail__value") ] [ HH.text value ]
    ]

renderMetric :: forall m. String -> String -> H.ComponentHTML Action () m
renderMetric value label =
  HH.div
    [ HP.class_ (H.ClassName "session-metric") ]
    [ HH.div [ HP.class_ (H.ClassName "session-metric__value") ] [ HH.text value ]
    , HH.div [ HP.class_ (H.ClassName "session-metric__label") ] [ HH.text label ]
    ]

renderMessage :: forall m. Set.Set String -> Message -> H.ComponentHTML Action () m
renderMessage expandedIds message =
  let
    isExpanded = Set.member message.id expandedIds
    roleIcon = case message.role of
      User -> "👤"
      Assistant -> "🤖"
      System -> "⚙️"
      Tool -> "🔧"
  in
    HH.div
      [ HP.classes $ messageClasses message.role
      , HE.onClick \_ -> ToggleMessageExpand message.id
      ]
      [ HH.div
          [ HP.class_ (H.ClassName "message__header") ]
          [ HH.span [ HP.class_ (H.ClassName "message__icon") ] [ HH.text roleIcon ]
          , HH.span [ HP.class_ (H.ClassName "message__content") ]
              [ HH.text $ truncateContent isExpanded message.content ]
          ]
      , HH.div
          [ HP.class_ (H.ClassName "message__footer") ]
          [ HH.span [ HP.class_ (H.ClassName "message__time") ]
              [ HH.text $ formatTime message.timestamp ]
          , case message.usage of
              Just usage -> renderMessageUsage usage
              Nothing -> HH.text ""
          ]
      , if not (Array.null message.toolCalls) then
          HH.div
            [ HP.class_ (H.ClassName "message__tools") ]
            (map renderToolCall message.toolCalls)
        else
          HH.text ""
      ]

renderMessageUsage :: forall m. MessageUsage -> H.ComponentHTML Action () m
renderMessageUsage usage =
  HH.span [ HP.class_ (H.ClassName "message__usage") ]
    [ HH.text $ formatNumber (toNumber usage.promptTokens) <> " in / "
        <> formatNumber (toNumber usage.completionTokens) <> " out"
        <> " │ " <> formatUSD usage.cost
    ]

renderToolCall :: forall m. ToolCall -> H.ComponentHTML Action () m
renderToolCall { name, status, durationMs } =
  HH.div
    [ HP.class_ (H.ClassName "tool-call") ]
    [ HH.span [ HP.class_ (H.ClassName "tool-call__icon") ]
        [ HH.text $ statusIcon status ]
    , HH.span [ HP.class_ (H.ClassName "tool-call__name") ]
        [ HH.text name ]
    , case durationMs of
        Just ms -> HH.span [ HP.class_ (H.ClassName "tool-call__duration") ]
            [ HH.text $ show ms <> "ms" ]
        Nothing -> HH.text ""
    ]

statusIcon :: ToolStatus -> String
statusIcon = case _ of
  Pending -> "⏳"
  Running -> "🔄"
  Completed -> "✓"
  Failed -> "✗"

messageClasses :: Role -> Array H.ClassName
messageClasses role =
  [ H.ClassName "message" ] <> case role of
    User -> [ H.ClassName "message--user" ]
    Assistant -> [ H.ClassName "message--assistant" ]
    System -> [ H.ClassName "message--system" ]
    Tool -> [ H.ClassName "message--tool" ]

truncateContent :: Boolean -> String -> String
truncateContent isExpanded content =
  if isExpanded
    then content
    else if Array.length (splitContent content) > 3
      then takeFirstLines 3 content <> "..."
      else content

splitContent :: String -> Array String
splitContent = String.split (String.Pattern "\n")

takeFirstLines :: Int -> String -> String
takeFirstLines n = String.joinWith "\n" <<< Array.take n <<< splitContent

toggleSet :: forall a. Ord a => a -> Set.Set a -> Set.Set a
toggleSet x set =
  if Set.member x set
    then Set.delete x set
    else Set.insert x set

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Get initial current time
    currentTime <- liftEffect getCurrentDateTime
    H.modify_ _ { currentTime = Just currentTime }
    -- Start periodic updates (every second)
    void $ H.fork $ startDurationTimer

  Receive session -> do
    H.modify_ _ { session = session }
    -- Update current time when session changes
    currentTime <- liftEffect getCurrentDateTime
    H.modify_ _ { currentTime = Just currentTime }

  ToggleMessageExpand id ->
    H.modify_ \s -> s { expandedMessages = toggleSet id s.expandedMessages }

  ExportSession -> do
    H.modify_ _ { isExporting = true }
    session <- H.gets _.session
    case session of
      Just s -> do
        -- Export to JSON
        let jsonContent = encodeSessionToJSON s
        let jsonFilename = "session-" <> s.id <> ".json"
        liftEffect $ downloadFile jsonContent jsonFilename
        
        -- Export to Markdown
        let markdownContent = encodeSessionToMarkdown s
        let markdownFilename = "session-" <> s.id <> ".md"
        liftEffect $ downloadFile markdownContent markdownFilename
        
        H.modify_ _ { isExporting = false }
        H.raise (SessionExported s.id)
      Nothing -> do
        H.modify_ _ { isExporting = false }

  ClearSession -> do
    H.raise SessionCleared

  UpdateCurrentTime dt ->
    H.modify_ _ { currentTime = Just dt }

-- | Start timer to update current time every second
startDurationTimer :: forall m. MonadAff m => H.HalogenM State Action () Output m Unit
startDurationTimer = do
  delay (Milliseconds 1000.0)
  currentTime <- liftEffect getCurrentDateTime
  H.modify_ _ { currentTime = Just currentTime }
  startDurationTimer  -- Recursive - keep updating

-- | Format duration between startedAt and current time
formatSessionDuration :: DateTime -> Maybe DateTime -> String
formatSessionDuration startedAt currentTime = case currentTime of
  Just now -> formatDuration startedAt now
  Nothing -> "Calculating..."  -- Show placeholder until currentTime is available

-- | Encode session to JSON string
encodeSessionToJSON :: Session -> String
encodeSessionToJSON session = show $ encodeJson
  { id: session.id
  , model: session.model
  , provider: session.provider
  , startedAt: toISOString session.startedAt
  , promptTokens: session.promptTokens
  , completionTokens: session.completionTokens
  , cost: session.cost
  , messages: map encodeMessage session.messages
  }
  where
    encodeMessage msg = encodeJson
      { id: msg.id
      , role: showRole msg.role
      , content: msg.content
      , timestamp: toISOString msg.timestamp
      , usage: map encodeUsage msg.usage
      , toolCalls: map encodeToolCall msg.toolCalls
      }
    encodeUsage usage = encodeJson
      { promptTokens: usage.promptTokens
      , completionTokens: usage.completionTokens
      , cost: usage.cost
      }
    encodeToolCall tool = encodeJson
      { name: tool.name
      , status: showToolStatus tool.status
      , durationMs: tool.durationMs
      }
    showRole = case _ of
      User -> "user"
      Assistant -> "assistant"
      System -> "system"
      Tool -> "tool"
    showToolStatus = case _ of
      Pending -> "pending"
      Running -> "running"
      Completed -> "completed"
      Failed -> "failed"

-- | Encode session to Markdown string
encodeSessionToMarkdown :: Session -> String
encodeSessionToMarkdown session =
  "# Session: " <> session.id <> "\n\n" <>
  "**Model:** " <> session.model <> "\n" <>
  "**Provider:** " <> session.provider <> "\n" <>
  "**Started:** " <> formatTime session.startedAt <> "\n" <>
  "**Prompt Tokens:** " <> show session.promptTokens <> "\n" <>
  "**Completion Tokens:** " <> show session.completionTokens <> "\n" <>
  "**Cost:** " <> formatUSD session.cost <> "\n\n" <>
  "## Messages\n\n" <>
  String.joinWith "\n\n" (map encodeMessageToMarkdown session.messages)
  where
    encodeMessageToMarkdown msg =
      "### " <> showRole msg.role <> " (" <> formatTime msg.timestamp <> ")\n\n" <>
      msg.content <> "\n" <>
      case msg.usage of
        Just usage -> "\n**Usage:** " <> show usage.promptTokens <> " in / " <> show usage.completionTokens <> " out | " <> formatUSD usage.cost <> "\n"
        Nothing -> "" <>
      if not (Array.null msg.toolCalls) then
        "\n**Tool Calls:**\n" <>
        String.joinWith "\n" (map (\tool -> "- " <> tool.name <> " (" <> showToolStatus tool.status <> ")") msg.toolCalls) <>
        "\n"
      else ""
    showRole = case _ of
      User -> "User"
      Assistant -> "Assistant"
      System -> "System"
      Tool -> "Tool"
    showToolStatus = case _ of
      Pending -> "Pending"
      Running -> "Running"
      Completed -> "Completed"
      Failed -> "Failed"
