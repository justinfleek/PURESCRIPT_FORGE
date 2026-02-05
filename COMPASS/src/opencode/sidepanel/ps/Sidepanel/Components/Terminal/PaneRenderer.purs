{-|
Module      : Sidepanel.Components.Terminal.PaneRenderer
Description : Render terminal panes with splitting UI
Renders pane layout as HTML with splitter handles for resizing.
-}
module Sidepanel.Components.Terminal.PaneRenderer where

import Prelude

import Data.Maybe (Maybe(..))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Sidepanel.Components.Terminal.PaneTypes
  ( PaneLayout(..)
  , PaneInfo
  , SplitDirection(..)
  , SplitInfo
  , PaneId
  )

-- | Render pane layout
renderPaneLayout :: forall m action. PaneLayout -> (PaneId -> action) -> (PaneId -> SplitDirection -> action) -> (PaneId -> SplitDirection -> Int -> action) -> H.ComponentHTML action () m
renderPaneLayout layout onPaneClick onSplit onResize = case layout of
  LeafPane info ->
    renderPane info onPaneClick
  
  SplitContainer splitInfo left right ->
    HH.div
      [ HP.class_ (H.ClassName ("pane-split-container " <> (if splitInfo.direction == Vertical then "split-vertical" else "split-horizontal")))
      , HP.style (getContainerStyle splitInfo)
      ]
      [ renderPaneLayout left onPaneClick onSplit onResize
      , renderSplitter splitInfo onResize
      , renderPaneLayout right onPaneClick onSplit onResize
      ]

-- | Render single pane
renderPane :: forall m action. PaneInfo -> (PaneId -> action) -> H.ComponentHTML action () m
renderPane info onPaneClick =
  HH.div
    [ HP.class_ (H.ClassName ("terminal-pane " <> (if info.isActive then "active" else "")))
    , HP.id_ info.id
    , HP.style ("width: " <> show info.size.width <> "px; height: " <> show info.size.height <> "px;")
    , HE.onClick \_ -> onPaneClick info.id
    ]
    [ HH.div
        [ HP.class_ (H.ClassName "pane-header") ]
        [ HH.text info.title ]
    , HH.div
        [ HP.class_ (H.ClassName "pane-content")
        , HP.id_ ("terminal-" <> info.id)
        ]
        []
    ]

-- | Render splitter handle
renderSplitter :: forall m action. SplitInfo -> (PaneId -> SplitDirection -> Int -> action) -> H.ComponentHTML action () m
renderSplitter splitInfo onResize =
  HH.div
    [ HP.class_ (H.ClassName ("pane-splitter " <> (if splitInfo.direction == Vertical then "splitter-vertical" else "splitter-horizontal")))
    , HP.style (getSplitterStyle splitInfo.direction)
    , HE.onMouseDown \_ -> onResize "dummy" splitInfo.direction 0  -- Would handle drag
    ]
    []

-- | Get container style
getContainerStyle :: SplitInfo -> String
getContainerStyle splitInfo =
  if splitInfo.direction == Vertical then
    "display: flex; flex-direction: row; width: 100%; height: 100%;"
  else
    "display: flex; flex-direction: column; width: 100%; height: 100%;"

-- | Get splitter style
getSplitterStyle :: SplitDirection -> String
getSplitterStyle direction =
  if direction == Vertical then
    "width: 4px; background: #333; cursor: col-resize; flex-shrink: 0;"
  else
    "height: 4px; background: #333; cursor: row-resize; flex-shrink: 0;"
