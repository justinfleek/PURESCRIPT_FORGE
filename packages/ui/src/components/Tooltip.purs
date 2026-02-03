-- | Tooltip Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/tooltip.tsx (87 lines)
-- |
-- | Informational tooltip that shows on hover/focus.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | - `data-component="tooltip-trigger"` - Trigger wrapper
-- | - `data-component="tooltip"` - Tooltip content
-- | - `data-placement` - Placement direction
-- | - `data-open` - Present when tooltip is visible
-- | - `data-slot="tooltip-keybind"` - Keybind content wrapper
-- | - `data-slot="tooltip-keybind-key"` - Keyboard shortcut text
module UI.Components.Tooltip
  ( component
  , Query(..)
  , Input
  , TooltipPlacement(..)
  , Slot
  , defaultInput
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tooltip placement options
data TooltipPlacement
  = Top
  | Bottom
  | Left
  | Right

derive instance eqTooltipPlacement :: Eq TooltipPlacement

placementToString :: TooltipPlacement -> String
placementToString Top = "top"
placementToString Bottom = "bottom"
placementToString Left = "left"
placementToString Right = "right"

-- | Tooltip input props
type Input =
  { content :: String              -- Tooltip text content
  , placement :: TooltipPlacement  -- Where to show tooltip
  , inactive :: Boolean            -- If true, tooltip is disabled
  , forceOpen :: Boolean           -- Force tooltip to stay open
  , className :: Maybe String      -- Trigger wrapper class
  , contentClass :: Maybe String   -- Tooltip content class
  }

defaultInput :: Input
defaultInput =
  { content: ""
  , placement: Top
  , inactive: false
  , forceOpen: false
  , className: Nothing
  , contentClass: Nothing
  }

-- | Queries for external control
data Query a
  = SetOpen Boolean a
  | IsOpen (Boolean -> a)

-- | Internal state
type State =
  { input :: Input
  , isHovered :: Boolean
  , isFocused :: Boolean
  }

-- | Internal actions
data Action
  = HandleMouseEnter
  | HandleMouseLeave
  | HandleFocusIn
  | HandleFocusOut
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
  , isHovered: false
  , isFocused: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  -- When inactive, just render children without tooltip wrapper
  if state.input.inactive
    then HH.div_ []  -- Empty - parent should provide children via slot
    else renderTooltip state

renderTooltip :: forall m. State -> H.ComponentHTML Action () m
renderTooltip state =
  let isOpen = state.input.forceOpen || state.isHovered || state.isFocused
  in
    HH.div
      [ HP.attr (HH.AttrName "data-component") "tooltip-trigger"
      , HP.attr (HH.AttrName "data-open") (if isOpen then "true" else "false")
      , HP.attr (HH.AttrName "style") "position: relative; display: inline-block;"
      , HE.onMouseEnter \_ -> HandleMouseEnter
      , HE.onMouseLeave \_ -> HandleMouseLeave
      , HE.onFocusIn \_ -> HandleFocusIn
      , HE.onFocusOut \_ -> HandleFocusOut
      ]
      ([ renderSlotPlaceholder state.input.className
       ] <> if isOpen then [ renderContent state ] else [])

-- | Placeholder for child content (slot)
renderSlotPlaceholder :: forall m. Maybe String -> H.ComponentHTML Action () m
renderSlotPlaceholder mClass =
  HH.div
    ([ HP.attr (HH.AttrName "data-slot") "tooltip-trigger-content"
     ] <> classAttr mClass)
    []

-- | Render tooltip content popup
renderContent :: forall m. State -> H.ComponentHTML Action () m
renderContent state =
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "tooltip"
     , HP.attr (HH.AttrName "data-placement") (placementToString state.input.placement)
     , HP.attr (HH.AttrName "role") "tooltip"
     , HP.attr (HH.AttrName "style") (positionStyle state.input.placement)
     ] <> classAttr state.input.contentClass)
    [ HH.text state.input.content ]

-- | CSS positioning based on placement
positionStyle :: TooltipPlacement -> String
positionStyle Top = 
  "position: absolute; bottom: 100%; left: 50%; transform: translateX(-50%); margin-bottom: 4px; z-index: 1000;"
positionStyle Bottom = 
  "position: absolute; top: 100%; left: 50%; transform: translateX(-50%); margin-top: 4px; z-index: 1000;"
positionStyle Left = 
  "position: absolute; right: 100%; top: 50%; transform: translateY(-50%); margin-right: 4px; z-index: 1000;"
positionStyle Right = 
  "position: absolute; left: 100%; top: 50%; transform: translateY(-50%); margin-left: 4px; z-index: 1000;"

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Void m Unit
handleAction = case _ of
  HandleMouseEnter ->
    H.modify_ _ { isHovered = true }

  HandleMouseLeave ->
    H.modify_ _ { isHovered = false }

  HandleFocusIn ->
    H.modify_ _ { isFocused = true }

  HandleFocusOut ->
    H.modify_ _ { isFocused = false }

  Receive newInput ->
    H.modify_ _ { input = newInput }

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Void m (Maybe a)
handleQuery = case _ of
  SetOpen open a -> do
    H.modify_ _ { isHovered = open }
    pure (Just a)

  IsOpen reply -> do
    state <- H.get
    let isOpen = state.input.forceOpen || state.isHovered || state.isFocused
    pure (Just (reply isOpen))

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs.
-- Positioning is handled via CSS.
-- Focus/hover events are handled by Halogen event handlers.
