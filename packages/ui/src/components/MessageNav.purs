-- | Message Navigation Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/message-nav.tsx (88 lines)
-- |
-- | Navigation component for browsing messages in a session.
-- | Supports normal and compact display modes with tooltip.
-- | Pure Halogen implementation.
-- |
-- | Data Attributes:
-- | - `data-component="message-nav"` - Root element
-- | - `data-size="normal|compact"` - Display size
-- | - `data-slot="message-nav-item"` - Navigation item
-- | - `data-slot="message-nav-tick-button"` - Compact tick button
-- | - `data-slot="message-nav-tick-line"` - Tick line indicator
-- | - `data-slot="message-nav-message-button"` - Normal message button
-- | - `data-slot="message-nav-title-preview"` - Title preview text
-- | - `data-active` - Active state indicator
module UI.Components.MessageNav
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , MessageNavSize(..)
  , UserMessage
  , MessageSummary
  , defaultInput
  ) where

import Prelude

import Data.Array (length)
import Data.Maybe (Maybe(..), fromMaybe)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import UI.Components.DiffChanges as DiffChanges

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Message summary with title and diffs
type MessageSummary =
  { title :: Maybe String
  , diffs :: Array DiffChanges.DiffChange
  }

-- | User message for navigation
type UserMessage =
  { id :: String
  , summary :: Maybe MessageSummary
  }

-- | Navigation size
data MessageNavSize
  = Normal
  | Compact

derive instance eqMessageNavSize :: Eq MessageNavSize

sizeToString :: MessageNavSize -> String
sizeToString Normal = "normal"
sizeToString Compact = "compact"

-- | Input props
type Input =
  { messages :: Array UserMessage
  , current :: Maybe String        -- ID of current message
  , size :: MessageNavSize
  , defaultLabel :: String         -- Label for messages without title
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { messages: []
  , current: Nothing
  , size: Normal
  , defaultLabel: "New message"
  , className: Nothing
  }

-- | Output events
data Output
  = MessageSelected String   -- Message ID

-- | Queries for external control
data Query a
  = SetCurrent (Maybe String) a
  | GetCurrent (Maybe String -> a)

-- | Internal state
type State =
  { input :: Input
  , hovering :: Boolean      -- For compact mode tooltip
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleClick String
  | HandleKeyPress String String   -- Message ID, Key
  | HandleMouseEnter
  | HandleMouseLeave

-- | Child slots (for DiffChanges)
type Slots = ( diffChanges :: forall q. H.Slot q Void Int )

-- | Slot type for parent components
type Slot id = H.Slot Query Output id

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
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { input
  , hovering: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.ul
    ([ HP.attr (HH.AttrName "role") "list"
    , HP.attr (HH.AttrName "data-component") "message-nav"
    , HP.attr (HH.AttrName "data-size") (sizeToString state.input.size)
    ] <> classAttr state.input.className)
    (mapWithIndex (renderItem state) state.input.messages)

renderItem :: forall m. MonadAff m => State -> Int -> UserMessage -> H.ComponentHTML Action Slots m
renderItem state index message =
  let
    isActive = state.input.current == Just message.id
    label = getMessageLabel state.input.defaultLabel message
  in
    HH.li
      [ HP.attr (HH.AttrName "data-slot") "message-nav-item" ]
      [ case state.input.size of
          Compact -> renderCompactItem state message isActive
          Normal -> renderNormalItem state index message isActive label
      ]

renderCompactItem :: forall m. State -> UserMessage -> Boolean -> H.ComponentHTML Action Slots m
renderCompactItem state message isActive =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "message-nav-tick-button"
    , HP.attr (HH.AttrName "data-active") (if isActive then "true" else "false")
    , HP.attr (HH.AttrName "role") "button"
    , HP.tabIndex 0
    , HE.onClick \_ -> HandleClick message.id
    ]
    [ HH.div
        [ HP.attr (HH.AttrName "data-slot") "message-nav-tick-line" ]
        []
    ]

renderNormalItem :: forall m. MonadAff m => State -> Int -> UserMessage -> Boolean -> String -> H.ComponentHTML Action Slots m
renderNormalItem state index message isActive label =
  HH.button
    [ HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "data-slot") "message-nav-message-button"
    , HE.onClick \_ -> HandleClick message.id
    ]
    [ -- Diff changes bars
      HH.slot_ (Proxy :: Proxy "diffChanges") index DiffChanges.component
        { changes: getDiffs message
        , variant: DiffChanges.Bars
        , className: Nothing
        }
    -- Title preview
    , HH.div
        [ HP.attr (HH.AttrName "data-slot") "message-nav-title-preview"
        , HP.attr (HH.AttrName "data-active") (if isActive then "true" else "false")
        ]
        [ HH.text label ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- HELPERS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get message label from summary or default
getMessageLabel :: String -> UserMessage -> String
getMessageLabel defaultLabel message =
  case message.summary of
    Nothing -> defaultLabel
    Just summary -> fromMaybe defaultLabel summary.title

-- | Get diffs from message summary
getDiffs :: UserMessage -> Array DiffChanges.DiffChange
getDiffs message =
  case message.summary of
    Nothing -> []
    Just summary -> summary.diffs

-- | Map with index
mapWithIndex :: forall a b. (Int -> a -> b) -> Array a -> Array b
mapWithIndex f arr = mapWithIndexImpl f arr 0

mapWithIndexImpl :: forall a b. (Int -> a -> b) -> Array a -> Int -> Array b
mapWithIndexImpl f arr idx = case uncons arr of
  Nothing -> []
  Just { head, tail } -> 
    [f idx head] <> mapWithIndexImpl f tail (idx + 1)

foreign import uncons :: forall a. Array a -> Maybe { head :: a, tail :: Array a }

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive newInput -> do
    H.modify_ _ { input = newInput }

  HandleClick messageId -> do
    H.raise (MessageSelected messageId)

  HandleKeyPress messageId key -> do
    when (key == "Enter" || key == " ") do
      H.raise (MessageSelected messageId)

  HandleMouseEnter -> do
    H.modify_ _ { hovering = true }

  HandleMouseLeave -> do
    H.modify_ _ { hovering = false }

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  SetCurrent mId a -> do
    state <- H.get
    H.modify_ _ { input = state.input { current = mId } }
    pure (Just a)

  GetCurrent reply -> do
    state <- H.get
    pure (Just (reply state.input.current))

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROXY
-- ═══════════════════════════════════════════════════════════════════════════════

data Proxy :: forall k. k -> Type
data Proxy a = Proxy

-- For Void (no output from child)
data Void
