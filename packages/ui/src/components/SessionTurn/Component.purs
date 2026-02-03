-- | SessionTurn Component Module
-- | Main session turn component.
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/session-turn.tsx
-- |
-- | Data Attributes:
-- | - data-component="session-turn": Root container
-- | - data-slot="session-turn-content": Scrollable content area
-- | - data-slot="session-turn-message-container": Message container
-- | - data-slot="session-turn-attachments": Attachment section
-- | - data-slot="session-turn-message-content": Message content
-- | - data-slot="session-turn-sticky": Sticky header area
-- | - data-slot="session-turn-response-trigger": Expand/collapse trigger
-- | - data-slot="session-turn-summary-section": Response summary
-- | - data-slot="session-turn-accordion": File diff accordion
-- | - data-message: Message ID attribute

module UI.Components.SessionTurn.Component
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  ) where

import Prelude

import Data.Array (filter, length, last)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import UI.Components.SessionTurn.Types (SessionStatus(..), SessionTurnProps, FileDiff)
import UI.Components.SessionTurn.Status (computeStatusFromPart, formatDuration)
import UI.Components.MessagePart.Types (Message, Part(..), TextPartData)

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

type Input = SessionTurnProps

data Output
  = StepsToggled Boolean
  | UserInteracted
  | CopyClicked String

data Query a
  = ForceScrollToBottom a
  | GetWorking (Boolean -> a)

type State =
  { input :: Input
  , status :: SessionStatus
  , rawStatus :: Maybe String
  , duration :: String
  , retrySeconds :: Int
  , diffsOpen :: Array String
  , diffLimit :: Int
  , copied :: Boolean
  }

data Action
  = Initialize
  | Finalize
  | Receive Input
  | HandleStepsToggle
  | HandleScroll
  | HandleInteraction
  | HandleCopy String
  | HandleDiffToggle String
  | HandleShowMoreDiffs
  | UpdateDuration
  | UpdateRetryCountdown

type Slot id = H.Slot Query Output id

-- Constants
diffInit :: Int
diffInit = 20

diffBatch :: Int
diffBatch = 20

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      , finalize = Just Finalize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { input
  , status: Idle
  , rawStatus: Nothing
  , duration: ""
  , retrySeconds: 0
  , diffsOpen: []
  , diffLimit: diffInit
  , copied: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    ([ HP.ref (H.RefLabel "root")
    , HP.attr (HH.AttrName "data-component") "session-turn"
    ] <> classAttr (state.input.classes >>= _.root))
    [ renderContent state ]

renderContent :: forall m. State -> H.ComponentHTML Action () m
renderContent state =
  HH.div
    ([ HP.ref (H.RefLabel "scroll")
    , HP.attr (HH.AttrName "data-slot") "session-turn-content"
    , HE.onScroll \_ -> HandleScroll
    ] <> classAttr (state.input.classes >>= _.content))
    [ HH.div
        [ HE.onClick \_ -> HandleInteraction ]
        [ renderMessageContainer state ]
    ]

renderMessageContainer :: forall m. State -> H.ComponentHTML Action () m
renderMessageContainer state =
  HH.div
    ([ HP.ref (H.RefLabel "container")
    , HP.attr (HH.AttrName "data-slot") "session-turn-message-container"
    , HP.attr (HH.AttrName "data-message") state.input.messageID
    ] <> classAttr (state.input.classes >>= _.container))
    [ renderStickySection state
    , renderCollapsibleContent state
    , renderSummarySection state
    ]

renderStickySection :: forall m. State -> H.ComponentHTML Action () m
renderStickySection state =
  HH.div
    [ HP.ref (H.RefLabel "sticky")
    , HP.attr (HH.AttrName "data-slot") "session-turn-sticky"
    ]
    [ renderMessageContent state
    , renderResponseTrigger state
    ]

renderMessageContent :: forall m. State -> H.ComponentHTML Action () m
renderMessageContent state =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "session-turn-message-content" ]
    [ HH.text "User message content" ]

renderResponseTrigger :: forall m. State -> H.ComponentHTML Action () m
renderResponseTrigger state =
  let working = isWorking state.status
      hasSteps = true -- Would be computed from parts
  in if not (working || hasSteps)
     then HH.text ""
     else HH.div
       [ HP.attr (HH.AttrName "data-slot") "session-turn-response-trigger" ]
       [ HH.button
           [ HP.type_ HP.ButtonButton
           , HP.attr (HH.AttrName "data-slot") "session-turn-collapsible-trigger-content"
           , HE.onClick \_ -> HandleStepsToggle
           ]
           [ renderStatusIndicator state
           , renderStatusText state
           , HH.span [] [ HH.text " · " ]
           , HH.span [] [ HH.text state.duration ]
           ]
       ]

renderStatusIndicator :: forall m. State -> H.ComponentHTML Action () m
renderStatusIndicator state =
  if isWorking state.status
    then HH.span [ HP.attr (HH.AttrName "data-slot") "spinner" ] [ HH.text "..." ]
    else HH.span [] [ HH.text "▼" ]

renderStatusText :: forall m. State -> H.ComponentHTML Action () m
renderStatusText state =
  case state.status of
    Retry r ->
      HH.span []
        [ HH.span 
            [ HP.attr (HH.AttrName "data-slot") "session-turn-retry-message" ]
            [ HH.text (truncate 60 r.message) ]
        , HH.span
            [ HP.attr (HH.AttrName "data-slot") "session-turn-retry-seconds" ]
            [ HH.text (" · Retrying" <> if state.retrySeconds > 0 then " in " <> show state.retrySeconds <> "s" else "") ]
        , HH.span
            [ HP.attr (HH.AttrName "data-slot") "session-turn-retry-attempt" ]
            [ HH.text (" (#" <> show r.attempt <> ")") ]
        ]
    Running ->
      HH.span
        [ HP.attr (HH.AttrName "data-slot") "session-turn-status-text" ]
        [ HH.text (fromMaybe "Considering next steps..." state.rawStatus) ]
    Idle ->
      HH.span
        [ HP.attr (HH.AttrName "data-slot") "session-turn-status-text" ]
        [ HH.text (if state.input.stepsExpanded then "Hide steps" else "Show steps") ]

renderCollapsibleContent :: forall m. State -> H.ComponentHTML Action () m
renderCollapsibleContent state =
  if not state.input.stepsExpanded
    then HH.text ""
    else HH.div
      [ HP.attr (HH.AttrName "data-slot") "session-turn-collapsible-content-inner" ]
      [ HH.text "Assistant message parts would render here" ]

renderSummarySection :: forall m. State -> H.ComponentHTML Action () m
renderSummarySection state =
  let working = isWorking state.status
  in if working
     then HH.text ""
     else HH.div
       [ HP.attr (HH.AttrName "data-slot") "session-turn-summary-section" ]
       [ HH.div
           [ HP.attr (HH.AttrName "data-slot") "session-turn-summary-header" ]
           [ HH.h2
               [ HP.attr (HH.AttrName "data-slot") "session-turn-summary-title" ]
               [ HH.text "Response" ]
           ]
       , renderDiffAccordion state
       ]

renderDiffAccordion :: forall m. State -> H.ComponentHTML Action () m
renderDiffAccordion state =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "session-turn-accordion" ]
    [ HH.text "Diff accordion would render here" ]

-- Helpers
classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

isWorking :: SessionStatus -> Boolean
isWorking Idle = false
isWorking Running = true
isWorking (Retry _) = true

truncate :: Int -> String -> String
truncate n s = 
  if length s > n
    then take n s <> "..."
    else s
  where
    length = Data.String.length
    take = Data.String.take

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Set up duration timer
    -- Set up retry countdown
    pure unit

  Finalize -> pure unit

  Receive newInput -> do
    state <- H.get
    -- Reset diff state on message change
    when (state.input.messageID /= newInput.messageID) do
      H.modify_ _ { diffsOpen = [], diffLimit = diffInit }
    H.modify_ _ { input = newInput }

  HandleStepsToggle -> do
    state <- H.get
    for_ state.input.onStepsExpandedToggle \toggle ->
      liftEffect toggle
    H.raise (StepsToggled (not state.input.stepsExpanded))

  HandleScroll -> pure unit

  HandleInteraction -> do
    state <- H.get
    for_ state.input.onUserInteracted \handler ->
      liftEffect handler
    H.raise UserInteracted

  HandleCopy content -> do
    liftEffect $ copyToClipboard content
    H.modify_ _ { copied = true }
    H.raise (CopyClicked content)

  HandleDiffToggle file -> do
    state <- H.get
    let current = state.diffsOpen
        next = if elem file current
               then filter (_ /= file) current
               else current <> [file]
    H.modify_ _ { diffsOpen = next }

  HandleShowMoreDiffs -> do
    state <- H.get
    H.modify_ _ { diffLimit = state.diffLimit + diffBatch }

  UpdateDuration -> pure unit

  UpdateRetryCountdown -> pure unit
  where
    elem x xs = isJust (find (_ == x) xs)
    find f xs = Data.Array.find f xs

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  ForceScrollToBottom a -> do
    liftEffect forceScrollToBottom
    pure (Just a)

  GetWorking reply -> do
    state <- H.get
    pure (Just (reply (isWorking state.status)))

-- ═══════════════════════════════════════════════════════════════════════════════
-- FFI
-- ═══════════════════════════════════════════════════════════════════════════════

foreign import copyToClipboard :: String -> Effect Unit
foreign import forceScrollToBottom :: Effect Unit
