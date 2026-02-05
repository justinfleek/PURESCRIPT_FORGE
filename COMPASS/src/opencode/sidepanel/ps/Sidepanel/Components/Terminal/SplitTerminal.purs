{-|
Module      : Sidepanel.Components.Terminal.SplitTerminal
Description : Main Halogen component for split terminal panes
Main component that manages terminal panes with tmux-style splitting.
-}
module Sidepanel.Components.Terminal.SplitTerminal where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Sidepanel.Components.Terminal.PaneTypes
  ( PaneState
  , PaneId
  , SplitDirection(..)
  , NavigationDirection(..)
  )
import Sidepanel.Components.Terminal.PaneManager
  ( initialPaneState
  , splitPaneVertically
  , splitPaneHorizontally
  , closePane
  , resizePane
  , swapPanes
  , navigateToPane
  , calculatePaneSizes
  )
import Sidepanel.Components.Terminal.PaneTypes (PaneSize)
import Sidepanel.Components.Terminal.PaneRenderer (renderPaneLayout)

-- | Component state
type State =
  { paneState :: PaneState
  , containerSize :: { width :: Int, height :: Int }
  }

-- | Component actions
data Action
  = Initialize
  | SplitVertical PaneId
  | SplitHorizontal PaneId
  | ClosePane PaneId
  | ResizePane PaneId SplitDirection Int
  | Navigate NavigationDirection
  | SwapPanes PaneId PaneId
  | ResizeContainer Int Int

-- | Component output
data Output
  = PaneCreated PaneId
  | PaneClosed PaneId
  | PaneActivated PaneId

-- | Component input
type Input = { initialPaneId :: PaneId }

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      { paneState: initialPaneState input.initialPaneId
          { id: input.initialPaneId
          , terminalId: "terminal-" <> input.initialPaneId
          , size: { width: 80, height: 24 }
          , isActive: true
          , title: "Terminal 1"
          }
      , containerSize: { width: 800, height: 600 }
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

-- | Render component
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "split-terminal-container")
    , HP.style ("width: " <> show state.containerSize.width <> "px; height: " <> show state.containerSize.height <> "px;")
    ]
    [ renderPaneLayout
        (calculatePaneSizes state.paneState.root { width: state.containerSize.width, height: state.containerSize.height })
        (\id -> SplitVertical id)  -- Click to split vertical
        (\id -> SplitHorizontal id)  -- Right-click to split horizontal
        (\id dir delta -> ResizePane id dir delta)
    , renderToolbar state
    ]

-- | Render toolbar
renderToolbar :: forall m. State -> H.ComponentHTML Action () m
renderToolbar state =
  HH.div
    [ HP.class_ (H.ClassName "pane-toolbar") ]
    [ HH.button
        [ HE.onClick \_ -> case state.paneState.activePaneId of
            Nothing -> Navigate Next
            Just id -> SplitVertical id
        ]
        [ HH.text "Split Vertical (Ctrl+B %)" ]
    , HH.button
        [ HE.onClick \_ -> case state.paneState.activePaneId of
            Nothing -> Navigate Next
            Just id -> SplitHorizontal id
        ]
        [ HH.text "Split Horizontal (Ctrl+B \")" ]
    , HH.button
        [ HE.onClick \_ -> case state.paneState.activePaneId of
            Nothing -> pure unit
            Just id -> ClosePane id
        ]
        [ HH.text "Close Pane (Ctrl+B x)" ]
    , HH.button
        [ HE.onClick \_ -> Navigate Up ]
        [ HH.text "Navigate Up" ]
    , HH.button
        [ HE.onClick \_ -> Navigate Down ]
        [ HH.text "Navigate Down" ]
    , HH.button
        [ HE.onClick \_ -> Navigate Left ]
        [ HH.text "Navigate Left" ]
    , HH.button
        [ HE.onClick \_ -> Navigate Right ]
        [ HH.text "Navigate Right" ]
    ]

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Initialize terminal instances for panes
    pure unit
  
  SplitVertical paneId -> do
    state <- H.get
    result <- H.lift $ splitPaneVertically state.paneState paneId
    if result.success then
      do
        H.modify_ \s -> s { paneState = result.newState }
        case result.newState.activePaneId of
          Just newId -> H.raise (PaneCreated newId)
          Nothing -> pure unit
    else
      pure unit
  
  SplitHorizontal paneId -> do
    state <- H.get
    result <- H.lift $ splitPaneHorizontally state.paneState paneId
    if result.success then
      do
        H.modify_ \s -> s { paneState = result.newState }
        case result.newState.activePaneId of
          Just newId -> H.raise (PaneCreated newId)
          Nothing -> pure unit
    else
      pure unit
  
  ClosePane paneId -> do
    state <- H.get
    result <- H.lift $ closePane state.paneState paneId
    if result.success then
      do
        H.modify_ \s -> s { paneState = result.newState }
        H.raise (PaneClosed paneId)
    else
      pure unit
  
  ResizePane paneId direction delta -> do
    state <- H.get
    result <- H.lift $ resizePane state.paneState paneId direction delta
    if result.success then
      H.modify_ \s -> s { paneState = result.newState }
    else
      pure unit
  
  Navigate direction -> do
    state <- H.get
    result <- H.lift $ navigateToPane state.paneState direction
    if result.success then
      do
        H.modify_ \s -> s { paneState = result.newState }
        case result.newState.activePaneId of
          Just newId -> H.raise (PaneActivated newId)
          Nothing -> pure unit
    else
      pure unit
  
  SwapPanes id1 id2 -> do
    state <- H.get
    result <- H.lift $ swapPanes state.paneState id1 id2
    if result.success then
      H.modify_ \s -> s { paneState = result.newState }
    else
      pure unit
  
  ResizeContainer width height -> do
    H.modify_ \s -> s { containerSize = { width: width, height: height } }

-- | Import renderer
import Sidepanel.Components.Terminal.PaneRenderer (renderPaneLayout)
import Sidepanel.Components.Terminal.PaneTypes (PaneSize)
