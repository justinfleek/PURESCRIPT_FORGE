-- | BasicTool Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/basic-tool.tsx (119 lines)
-- |
-- | Collapsible tool display with icon, title, and optional details.
-- | Built on Collapsible primitive.
-- |
-- | Data Attributes:
-- | - `data-component="tool-trigger"` - Trigger container
-- | - `data-slot="basic-tool-tool-trigger-content"` - Content wrapper
-- | - `data-slot="basic-tool-tool-info"` - Info container
-- | - `data-slot="basic-tool-tool-info-structured"` - Structured info
-- | - `data-slot="basic-tool-tool-info-main"` - Main info row
-- | - `data-slot="basic-tool-tool-title"` - Title text
-- | - `data-slot="basic-tool-tool-subtitle"` - Subtitle text (clickable)
-- | - `data-slot="basic-tool-tool-arg"` - Argument badge
module UI.Components.BasicTool
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , TriggerTitle
  , defaultInput
  , defaultTriggerTitle
  ) where

import Prelude

import Data.Array (length)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..), fromMaybe)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import UI.Components.Icon as Icon

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Structured trigger title
type TriggerTitle =
  { title :: String
  , titleClass :: Maybe String
  , subtitle :: Maybe String
  , subtitleClass :: Maybe String
  , args :: Array String
  , argsClass :: Maybe String
  }

defaultTriggerTitle :: TriggerTitle
defaultTriggerTitle =
  { title: ""
  , titleClass: Nothing
  , subtitle: Nothing
  , subtitleClass: Nothing
  , args: []
  , argsClass: Nothing
  }

-- | BasicTool input props
type Input =
  { icon :: Icon.IconName         -- Icon to display
  , trigger :: TriggerTitle       -- Title structure
  , hideDetails :: Boolean        -- Hide collapsible content
  , defaultOpen :: Boolean        -- Initial open state
  , forceOpen :: Boolean          -- Force open state
  , locked :: Boolean             -- Prevent closing
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { icon: "mcp"
  , trigger: defaultTriggerTitle
  , hideDetails: false
  , defaultOpen: false
  , forceOpen: false
  , locked: false
  , className: Nothing
  }

-- | Output events
data Output
  = OpenChanged Boolean
  | SubtitleClicked

-- | Queries for external control
data Query a
  = Open a
  | Close a
  | Toggle a
  | IsOpen (Boolean -> a)

-- | Internal state
type State =
  { input :: Input
  , isOpen :: Boolean
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleToggle
  | HandleSubtitleClick

-- | Child slots (for Icon component)
type Slots = ( icon :: Icon.Slot Unit )

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
  , isOpen: input.defaultOpen || input.forceOpen
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "basic-tool"
    , HP.attr (HH.AttrName "data-state") (if state.isOpen then "open" else "closed")
    ] <> classAttr state.input.className)
    [ renderTrigger state
    , renderContent state
    ]

renderTrigger :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderTrigger state =
  HH.button
    [ HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "data-component") "tool-trigger"
    , HP.disabled (state.input.hideDetails || state.input.locked)
    , HE.onClick \_ -> HandleToggle
    ]
    [ HH.div
        [ HP.attr (HH.AttrName "data-slot") "basic-tool-tool-trigger-content" ]
        [ HH.slot (Proxy :: Proxy "icon") unit Icon.component
            { name: state.input.icon
            , size: Icon.Small
            , className: Nothing
            }
            absurd
        , HH.div
            [ HP.attr (HH.AttrName "data-slot") "basic-tool-tool-info" ]
            [ renderStructuredInfo state ]
        ]
    , renderArrow state
    ]

renderStructuredInfo :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderStructuredInfo state =
  let trigger = state.input.trigger
  in
    HH.div
      [ HP.attr (HH.AttrName "data-slot") "basic-tool-tool-info-structured" ]
      [ HH.div
          [ HP.attr (HH.AttrName "data-slot") "basic-tool-tool-info-main" ]
          [ -- Title
            HH.span
              ([ HP.attr (HH.AttrName "data-slot") "basic-tool-tool-title"
              ] <> classAttr trigger.titleClass)
              [ HH.text trigger.title ]
          -- Subtitle (if present)
          , case trigger.subtitle of
              Nothing -> HH.text ""
              Just subtitle ->
                HH.span
                  ([ HP.attr (HH.AttrName "data-slot") "basic-tool-tool-subtitle"
                  , HP.class_ (HH.ClassName "clickable")
                  , HE.onClick \e -> HandleSubtitleClick
                  ] <> classAttr trigger.subtitleClass)
                  [ HH.text subtitle ]
          -- Args (if present)
          , if length trigger.args > 0
              then HH.span_ (map (renderArg trigger.argsClass) trigger.args)
              else HH.text ""
          ]
      ]

renderArg :: forall w i. Maybe String -> String -> HH.HTML w i
renderArg mClass arg =
  HH.span
    ([ HP.attr (HH.AttrName "data-slot") "basic-tool-tool-arg"
    ] <> classAttr mClass)
    [ HH.text arg ]

renderArrow :: forall m. State -> H.ComponentHTML Action Slots m
renderArrow state =
  if state.input.hideDetails || state.input.locked
    then HH.text ""
    else
      HH.span
        [ HP.attr (HH.AttrName "data-slot") "basic-tool-arrow"
        , HP.attr (HH.AttrName "aria-hidden") "true"
        ]
        [ HH.text (if state.isOpen then "▼" else "▶") ]

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  if state.isOpen && not state.input.hideDetails
    then
      HH.div
        [ HP.attr (HH.AttrName "data-slot") "basic-tool-content"
        , HP.attr (HH.AttrName "data-state") "open"
        ]
        [ HH.text "Tool details content" ]  -- Slot for children in real implementation
    else HH.text ""

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
    state <- H.get
    -- Handle forceOpen
    when newInput.forceOpen do
      H.modify_ _ { isOpen = true }
    H.modify_ _ { input = newInput }

  HandleToggle -> do
    state <- H.get
    -- Don't close if locked
    unless (state.input.locked && state.isOpen) do
      let newOpen = not state.isOpen
      H.modify_ _ { isOpen = newOpen }
      H.raise (OpenChanged newOpen)

  HandleSubtitleClick -> do
    H.raise SubtitleClicked

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  Open a -> do
    H.modify_ _ { isOpen = true }
    H.raise (OpenChanged true)
    pure (Just a)

  Close a -> do
    state <- H.get
    unless state.input.locked do
      H.modify_ _ { isOpen = false }
      H.raise (OpenChanged false)
    pure (Just a)

  Toggle a -> do
    handleAction HandleToggle
    pure (Just a)

  IsOpen reply -> do
    state <- H.get
    pure (Just (reply state.isOpen))

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROXY
-- ═══════════════════════════════════════════════════════════════════════════════

data Proxy :: forall k. k -> Type
data Proxy a = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs.
-- Built on top of existing Icon component.
