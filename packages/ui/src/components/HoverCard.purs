-- | HoverCard Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/hover-card.tsx (33 lines)
-- |
-- | Card that appears on hover with rich content.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-slot="hover-card-trigger"` - Trigger element
-- | - `data-component="hover-card-content"` - Content container
-- | - `data-slot="hover-card-body"` - Body content
-- | - `data-open="true|false"` - Open state
module UI.Components.HoverCard
  ( component
  , Query(..)
  , Input
  , Slot
  , defaultInput
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff (Milliseconds(..), delay)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Aff.AVar as AVar
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | HoverCard input props
type Input =
  { openDelay :: Int      -- Delay before opening (ms)
  , closeDelay :: Int     -- Delay before closing (ms)
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { openDelay: 300
  , closeDelay: 300
  , className: Nothing
  }

-- | Queries for external control
data Query a
  = SetOpen Boolean a
  | IsOpen (Boolean -> a)

-- | Internal state
type State =
  { input :: Input
  , isOpen :: Boolean
  , isHoveringTrigger :: Boolean
  , isHoveringContent :: Boolean
  , pendingClose :: Boolean
  }

-- | Internal actions
data Action
  = HandleTriggerMouseEnter
  | HandleTriggerMouseLeave
  | HandleContentMouseEnter
  | HandleContentMouseLeave
  | OpenAfterDelay
  | CloseAfterDelay
  | Receive Input

-- | Slot type for parent components
type Slot id = H.Slot Query Void id

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

component :: forall m. MonadAff m => H.Component Query Input Void m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { input
  , isOpen: false
  , isHoveringTrigger: false
  , isHoveringContent: false
  , pendingClose: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.attr (HH.AttrName "data-component") "hover-card-root"
    , HP.attr (HH.AttrName "data-open") (if state.isOpen then "true" else "false")
    , HP.attr (HH.AttrName "style") "position: relative; display: inline-block;"
    ]
    [ renderTrigger state
    , if state.isOpen then renderContent state else HH.text ""
    ]

renderTrigger :: forall m. State -> H.ComponentHTML Action () m
renderTrigger _ =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "hover-card-trigger"
    , HE.onMouseEnter \_ -> HandleTriggerMouseEnter
    , HE.onMouseLeave \_ -> HandleTriggerMouseLeave
    ]
    []  -- Trigger content provided by parent

renderContent :: forall m. State -> H.ComponentHTML Action () m
renderContent state =
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "hover-card-content"
     , HP.attr (HH.AttrName "style") contentStyle
     , HE.onMouseEnter \_ -> HandleContentMouseEnter
     , HE.onMouseLeave \_ -> HandleContentMouseLeave
     ] <> classAttr state.input.className)
    [ HH.div
        [ HP.attr (HH.AttrName "data-slot") "hover-card-body" ]
        []  -- Body content provided by parent
    ]
  where
    contentStyle = "position: absolute; top: 100%; left: 0; margin-top: 4px; z-index: 1000;"

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Void m Unit
handleAction = case _ of
  HandleTriggerMouseEnter -> do
    H.modify_ _ { isHoveringTrigger = true, pendingClose = false }
    handleAction OpenAfterDelay

  HandleTriggerMouseLeave -> do
    H.modify_ _ { isHoveringTrigger = false }
    handleAction CloseAfterDelay

  HandleContentMouseEnter -> do
    H.modify_ _ { isHoveringContent = true, pendingClose = false }

  HandleContentMouseLeave -> do
    H.modify_ _ { isHoveringContent = false }
    handleAction CloseAfterDelay

  OpenAfterDelay -> do
    state <- H.get
    liftAff $ delay (Milliseconds (toNumber state.input.openDelay))
    -- Check if still hovering after delay
    currentState <- H.get
    when currentState.isHoveringTrigger do
      H.modify_ _ { isOpen = true }

  CloseAfterDelay -> do
    state <- H.get
    H.modify_ _ { pendingClose = true }
    liftAff $ delay (Milliseconds (toNumber state.input.closeDelay))
    -- Check if should still close
    currentState <- H.get
    when (currentState.pendingClose && not currentState.isHoveringTrigger && not currentState.isHoveringContent) do
      H.modify_ _ { isOpen = false, pendingClose = false }

  Receive newInput ->
    H.modify_ _ { input = newInput }

-- Helper for Int to Number conversion
toNumber :: Int -> Number
toNumber = toNumberImpl

foreign import toNumberImpl :: Int -> Number

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Void m (Maybe a)
handleQuery = case _ of
  SetOpen open a -> do
    H.modify_ _ { isOpen = open }
    pure (Just a)

  IsOpen reply -> do
    state <- H.get
    pure (Just (reply state.isOpen))

-- ═══════════════════════════════════════════════════════════════════════════════
-- MINIMAL FFI
-- ═══════════════════════════════════════════════════════════════════════════════
-- Only Int to Number conversion needed
