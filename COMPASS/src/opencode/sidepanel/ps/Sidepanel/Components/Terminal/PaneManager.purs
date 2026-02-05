{-|
Module      : Sidepanel.Components.Terminal.PaneManager
Description : Core pane management operations (tmux-style)
Implements pane splitting, resizing, swapping, and navigation operations.
-}
module Sidepanel.Components.Terminal.PaneManager where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Sidepanel.Components.Terminal.PaneTypes
  ( PaneState
  , PaneLayout(..)
  , PaneInfo
  , SplitDirection(..)
  , SplitInfo
  , PaneId
  , PaneSize
  , NavigationDirection(..)
  , PaneOperationResult
  )

-- | Initial pane state
initialPaneState :: PaneId -> PaneInfo -> PaneState
initialPaneState paneId paneInfo =
  { root: LeafPane paneInfo
  , activePaneId: Just paneId
  , nextPaneId: 1
  , panes: [Tuple paneId paneInfo]
  }

-- | Split pane vertically
splitPaneVertically :: PaneState -> PaneId -> Aff PaneOperationResult
splitPaneVertically state targetPaneId = do
  let newPaneId = generatePaneId state.nextPaneId
  let newPane = createNewPane newPaneId
  let updatedState = state { nextPaneId = state.nextPaneId + 1 }
  
  case findAndSplitPane updatedState.root targetPaneId Vertical newPane of
    Nothing -> pure
      { success: false
      , newState: state
      , error: Just ("Pane not found: " <> targetPaneId)
      }
    Just newRoot -> do
      let newPanes = updatedState.panes <> [Tuple newPaneId newPane]
      pure
        { success: true
        , newState: updatedState
            { root = newRoot
            , panes = newPanes
            , activePaneId = Just newPaneId
            }
        , error: Nothing
        }

-- | Split pane horizontally
splitPaneHorizontally :: PaneState -> PaneId -> Aff PaneOperationResult
splitPaneHorizontally state targetPaneId = do
  let newPaneId = generatePaneId state.nextPaneId
  let newPane = createNewPane newPaneId
  let updatedState = state { nextPaneId = state.nextPaneId + 1 }
  
  case findAndSplitPane updatedState.root targetPaneId Horizontal newPane of
    Nothing -> pure
      { success: false
      , newState: state
      , error: Just ("Pane not found: " <> targetPaneId)
      }
    Just newRoot -> do
      let newPanes = updatedState.panes <> [Tuple newPaneId newPane]
      pure
        { success: true
        , newState: updatedState
            { root = newRoot
            , panes = newPanes
            , activePaneId = Just newPaneId
            }
        , error: Nothing
        }

-- | Find pane and split it
findAndSplitPane :: PaneLayout -> PaneId -> SplitDirection -> PaneInfo -> Maybe PaneLayout
findAndSplitPane layout targetId direction newPane = case layout of
  LeafPane info ->
    if info.id == targetId then
      Just (SplitContainer
        { direction: direction
        , splitRatio: 0.5
        , isResizing: false
        }
        (LeafPane info)
        (LeafPane newPane)
      )
    else
      Nothing
  
  SplitContainer splitInfo left right ->
    case findAndSplitPane left targetId direction newPane of
      Just newLeft -> Just (SplitContainer splitInfo newLeft right)
      Nothing -> case findAndSplitPane right targetId direction newPane of
        Just newRight -> Just (SplitContainer splitInfo left newRight)
        Nothing -> Nothing

-- | Close pane
closePane :: PaneState -> PaneId -> Aff PaneOperationResult
closePane state targetPaneId = do
  case removePaneFromLayout state.root targetPaneId of
    Nothing -> pure
      { success: false
      , newState: state
      , error: Just ("Pane not found: " <> targetPaneId)
      }
    Just newRoot -> do
      let remainingPanes = Array.filter (\(id /\ _) -> id /= targetPaneId) state.panes
      let newActiveId = case remainingPanes of
            [] -> Nothing
            (Tuple firstId _) : _ -> Just firstId
      
      pure
        { success: true
        , newState: state
            { root = newRoot
            , panes = remainingPanes
            , activePaneId = newActiveId
            }
        , error: Nothing
        }

-- | Remove pane from layout
removePaneFromLayout :: PaneLayout -> PaneId -> Maybe PaneLayout
removePaneFromLayout layout targetId = case layout of
  LeafPane info ->
    if info.id == targetId then
      Nothing  -- Can't remove last pane
    else
      Just layout
  
  SplitContainer splitInfo left right ->
    case removePaneFromLayout left targetId of
      Just newLeft -> Just (SplitContainer splitInfo newLeft right)
      Nothing -> case removePaneFromLayout right targetId of
        Just newRight -> Just (SplitContainer splitInfo left newRight)
        Nothing -> Nothing  -- Both children removed, collapse container

-- | Resize pane
resizePane :: PaneState -> PaneId -> SplitDirection -> Int -> Aff PaneOperationResult
resizePane state targetPaneId direction delta = do
  case adjustSplitRatio state.root targetPaneId direction delta of
    Nothing -> pure
      { success: false
      , newState: state
      , error: Just ("Pane not found or cannot resize: " <> targetPaneId)
      }
    Just newRoot -> do
      pure
        { success: true
        , newState: state { root = newRoot }
        , error: Nothing
        }

-- | Adjust split ratio
adjustSplitRatio :: PaneLayout -> PaneId -> SplitDirection -> Int -> Maybe PaneLayout
adjustSplitRatio layout targetId direction delta = case layout of
  LeafPane _ -> Nothing
  
  SplitContainer splitInfo left right ->
    if splitInfo.direction == direction then
      -- This container matches the resize direction
      let newRatio = clamp 0.1 0.9 (splitInfo.splitRatio + (Number.fromInt delta / 100.0))
      in Just (SplitContainer splitInfo { splitRatio = newRatio } left right)
    else
      -- Try children
      case adjustSplitRatio left targetId direction delta of
        Just newLeft -> Just (SplitContainer splitInfo newLeft right)
        Nothing -> case adjustSplitRatio right targetId direction delta of
          Just newRight -> Just (SplitContainer splitInfo left newRight)
          Nothing -> Nothing

-- | Swap panes
swapPanes :: PaneState -> PaneId -> PaneId -> Aff PaneOperationResult
swapPanes state id1 id2 = do
  case swapPanesInLayout state.root id1 id2 of
    Nothing -> pure
      { success: false
      , newState: state
      , error: Just ("Could not swap panes: " <> id1 <> " and " <> id2)
      }
    Just newRoot -> do
      pure
        { success: true
        , newState: state { root = newRoot }
        , error: Nothing
        }

-- | Swap panes in layout
swapPanesInLayout :: PaneLayout -> PaneId -> PaneId -> Maybe PaneLayout
swapPanesInLayout layout id1 id2 = case layout of
  LeafPane info ->
    if info.id == id1 then Just (LeafPane info { id = id2 })
    else if info.id == id2 then Just (LeafPane info { id = id1 })
    else Just layout
  
  SplitContainer splitInfo left right ->
    case swapPanesInLayout left id1 id2 of
      Just newLeft -> case swapPanesInLayout right id1 id2 of
        Just newRight -> Just (SplitContainer splitInfo newLeft newRight)
        Nothing -> Nothing
      Nothing -> Nothing

-- | Navigate to pane in direction
navigateToPane :: PaneState -> NavigationDirection -> Aff PaneOperationResult
navigateToPane state direction = do
  case state.activePaneId of
    Nothing -> pure
      { success: false
      , newState: state
      , error: Just "No active pane"
      }
    Just activeId -> do
      case findPaneInDirection state.root activeId direction of
        Nothing -> pure
          { success: false
          , newState: state
          , error: Just ("No pane found in direction: " <> show direction)
          }
        Just newActiveId -> do
          pure
            { success: true
            , newState: state { activePaneId = Just newActiveId }
            , error: Nothing
            }

-- | Find pane in direction
findPaneInDirection :: PaneLayout -> PaneId -> NavigationDirection -> Maybe PaneId
findPaneInDirection layout targetId direction = case layout of
  LeafPane info ->
    if info.id == targetId then Nothing  -- Found target, but no neighbor
    else Nothing
  
  SplitContainer splitInfo left right ->
    case findPaneInDirection left targetId direction of
      Just found -> Just found
      Nothing -> if isPaneInLayout left targetId then
        -- Target is in left, check if we should go to right
        if shouldNavigateToSibling splitInfo.direction direction then
          getFirstPaneId right
        else
          findPaneInDirection right targetId direction
      else
        findPaneInDirection right targetId direction

-- | Check if should navigate to sibling
shouldNavigateToSibling :: SplitDirection -> NavigationDirection -> Boolean
shouldNavigateToSibling splitDir navDir = case splitDir, navDir of
  Vertical, Right -> true
  Vertical, Left -> true
  Horizontal, Down -> true
  Horizontal, Up -> true
  _, _ -> false

-- | Get first pane ID from layout
getFirstPaneId :: PaneLayout -> Maybe PaneId
getFirstPaneId = case _ of
  LeafPane info -> Just info.id
  SplitContainer _ left _ -> getFirstPaneId left

-- | Check if pane is in layout
isPaneInLayout :: PaneLayout -> PaneId -> Boolean
isPaneInLayout layout targetId = case layout of
  LeafPane info -> info.id == targetId
  SplitContainer _ left right -> isPaneInLayout left targetId || isPaneInLayout right targetId

-- | Generate pane ID
generatePaneId :: Int -> PaneId
generatePaneId n = "pane-" <> show n

-- | Create new pane
createNewPane :: PaneId -> PaneInfo
createNewPane id =
  { id: id
  , terminalId: "terminal-" <> id
  , size: { width: 80, height: 24 }
  , isActive: false
  , title: "Terminal " <> id
  }

-- | Calculate pane sizes from layout
calculatePaneSizes :: PaneLayout -> PaneSize -> PaneLayout
calculatePaneSizes layout containerSize = case layout of
  LeafPane info -> LeafPane (info { size = containerSize })
  
  SplitContainer splitInfo left right ->
    let leftSize = calculateChildSize containerSize splitInfo.direction splitInfo.splitRatio true
        rightSize = calculateChildSize containerSize splitInfo.direction splitInfo.splitRatio false
        newLeft = calculatePaneSizes left leftSize
        newRight = calculatePaneSizes right rightSize
    in
      SplitContainer splitInfo newLeft newRight

-- | Calculate child size
calculateChildSize :: PaneSize -> SplitDirection -> Number -> Boolean -> PaneSize
calculateChildSize containerSize direction ratio isFirst = case direction of
  Vertical ->
    let width = if isFirst then
          Number.floor (Number.fromInt containerSize.width * ratio)
        else
          containerSize.width - Number.floor (Number.fromInt containerSize.width * ratio)
    in
      { width: width, height: containerSize.height }
  
  Horizontal ->
    let height = if isFirst then
          Number.floor (Number.fromInt containerSize.height * ratio)
        else
          containerSize.height - Number.floor (Number.fromInt containerSize.height * ratio)
    in
      { width: containerSize.width, height: height }

-- | Clamp number between min and max
clamp :: Number -> Number -> Number -> Number
clamp min max value =
  if value < min then min
  else if value > max then max
  else value
