{-|
Module      : Sidepanel.Components.Terminal.PaneLayouts
Description : Predefined pane layouts (tmux-style)
Implements predefined pane layouts for quick reorganization.
-}
module Sidepanel.Components.Terminal.PaneLayouts where

import Prelude

import Data.Array as Array
import Effect.Aff (Aff)
import Sidepanel.Components.Terminal.PaneTypes
  ( PaneLayout(..)
  , PaneInfo
  , SplitDirection(..)
  , SplitInfo
  , PaneState
  )

-- | Pane layout type
data PaneLayoutType
  = Tiled  -- Evenly sized panes
  | EvenHorizontal  -- Even horizontal splits
  | EvenVertical  -- Even vertical splits
  | MainHorizontal  -- One large pane on top, smaller below
  | MainVertical  -- One large pane on left, smaller on right

derive instance eqPaneLayoutType :: Eq PaneLayoutType

-- | Apply layout to pane state
applyLayout :: PaneState -> PaneLayoutType -> Aff PaneState
applyLayout state layoutType = do
  let panes = state.panes
  case Array.length panes of
    0 -> pure state
    1 -> pure state  -- Single pane, no layout needed
    _ -> do
      let newRoot = buildLayoutForPanes panes layoutType
      pure state { root = newRoot }

-- | Build layout for panes
buildLayoutForPanes :: Array (String /\ PaneInfo) -> PaneLayoutType -> PaneLayout
buildLayoutForPanes panes layoutType = case layoutType of
  Tiled -> buildTiledLayout panes
  EvenHorizontal -> buildEvenHorizontalLayout panes
  EvenVertical -> buildEvenVerticalLayout panes
  MainHorizontal -> buildMainHorizontalLayout panes
  MainVertical -> buildMainVerticalLayout panes

-- | Build tiled layout (evenly sized)
buildTiledLayout :: Array (String /\ PaneInfo) -> PaneLayout
buildTiledLayout panes = case Array.length panes of
  0 -> LeafPane { id: "empty", terminalId: "", size: { width: 0, height: 0 }, isActive: false, title: "" }
  1 -> LeafPane (snd (fromMaybe ("empty" /\ { id: "empty", terminalId: "", size: { width: 0, height: 0 }, isActive: false, title: "" }) (Array.head panes)))
  _ -> do
    let firstPane = fromMaybe ("empty" /\ { id: "empty", terminalId: "", size: { width: 0, height: 0 }, isActive: false, title: "" }) (Array.head panes)
    let remainingPanes = Array.drop 1 panes
    let left = LeafPane (snd firstPane)
    let right = buildTiledLayout remainingPanes
    SplitContainer
      { direction: Vertical
      , splitRatio: 1.0 / Number.fromInt (Array.length panes)
      , isResizing: false
      }
      left
      right

-- | Build even horizontal layout
buildEvenHorizontalLayout :: Array (String /\ PaneInfo) -> PaneLayout
buildEvenHorizontalLayout panes = case Array.length panes of
  0 -> LeafPane { id: "empty", terminalId: "", size: { width: 0, height: 0 }, isActive: false, title: "" }
  1 -> LeafPane (snd (fromMaybe ("empty" /\ { id: "empty", terminalId: "", size: { width: 0, height: 0 }, isActive: false, title: "" }) (Array.head panes)))
  _ -> do
    let firstPane = fromMaybe ("empty" /\ { id: "empty", terminalId: "", size: { width: 0, height: 0 }, isActive: false, title: "" }) (Array.head panes)
    let remainingPanes = Array.drop 1 panes
    let top = LeafPane (snd firstPane)
    let bottom = buildEvenHorizontalLayout remainingPanes
    SplitContainer
      { direction: Horizontal
      , splitRatio: 1.0 / Number.fromInt (Array.length panes)
      , isResizing: false
      }
      top
      bottom

-- | Build even vertical layout
buildEvenVerticalLayout :: Array (String /\ PaneInfo) -> PaneLayout
buildEvenVerticalLayout panes = buildTiledLayout panes  -- Same as tiled

-- | Build main horizontal layout (one large on top)
buildMainHorizontalLayout :: Array (String /\ PaneInfo) -> PaneLayout
buildMainHorizontalLayout panes = case Array.length panes of
  0 -> LeafPane { id: "empty", terminalId: "", size: { width: 0, height: 0 }, isActive: false, title: "" }
  1 -> LeafPane (snd (fromMaybe ("empty" /\ { id: "empty", terminalId: "", size: { width: 0, height: 0 }, isActive: false, title: "" }) (Array.head panes)))
  _ -> do
    let firstPane = fromMaybe ("empty" /\ { id: "empty", terminalId: "", size: { width: 0, height: 0 }, isActive: false, title: "" }) (Array.head panes)
    let remainingPanes = Array.drop 1 panes
    let mainPane = LeafPane (snd firstPane)
    let otherPanes = buildEvenHorizontalLayout remainingPanes
    SplitContainer
      { direction: Horizontal
      , splitRatio: 0.7  -- Main pane takes 70%
      , isResizing: false
      }
      mainPane
      otherPanes

-- | Build main vertical layout (one large on left)
buildMainVerticalLayout :: Array (String /\ PaneInfo) -> PaneLayout
buildMainVerticalLayout panes = case Array.length panes of
  0 -> LeafPane { id: "empty", terminalId: "", size: { width: 0, height: 0 }, isActive: false, title: "" }
  1 -> LeafPane (snd (fromMaybe ("empty" /\ { id: "empty", terminalId: "", size: { width: 0, height: 0 }, isActive: false, title: "" }) (Array.head panes)))
  _ -> do
    let firstPane = fromMaybe ("empty" /\ { id: "empty", terminalId: "", size: { width: 0, height: 0 }, isActive: false, title: "" }) (Array.head panes)
    let remainingPanes = Array.drop 1 panes
    let mainPane = LeafPane (snd firstPane)
    let otherPanes = buildEvenVerticalLayout remainingPanes
    SplitContainer
      { direction: Vertical
      , splitRatio: 0.7  -- Main pane takes 70%
      , isResizing: false
      }
      mainPane
      otherPanes

-- | Cycle through layouts
cycleLayout :: PaneState -> Aff PaneState
cycleLayout state = do
  let currentLayout = detectCurrentLayout state.root
  let nextLayout = getNextLayout currentLayout
  applyLayout state nextLayout

-- | Detect current layout type
detectCurrentLayout :: PaneLayout -> PaneLayoutType
detectCurrentLayout = case _ of
  LeafPane _ -> Tiled  -- Single pane
  SplitContainer splitInfo _ _ ->
    if splitInfo.direction == Horizontal then
      if splitInfo.splitRatio > 0.6 then MainHorizontal else EvenHorizontal
    else
      if splitInfo.splitRatio > 0.6 then MainVertical else EvenVertical

-- | Get next layout in cycle
getNextLayout :: PaneLayoutType -> PaneLayoutType
getNextLayout = case _ of
  Tiled -> EvenHorizontal
  EvenHorizontal -> EvenVertical
  EvenVertical -> MainHorizontal
  MainHorizontal -> MainVertical
  MainVertical -> Tiled

-- | Import utilities
import Data.Maybe (fromMaybe)
import Data.Number as Number
