{-|
Module      : Sidepanel.Components.Editor.MarkPointSystem
Description : Emacs-style mark & point system
Implements mark & point system for precise region operations.
-}
module Sidepanel.Components.Editor.MarkPointSystem where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Class (liftEffect)
import Sidepanel.Components.Editor.MarkPointSystemTypes
  ( MarkPointState
  , Mark
  , Position
  , Region
  )

-- | Initial mark & point state
initialMarkPointState :: MarkPointState
initialMarkPointState =
  { point: { file: "", line: 0, column: 0 }
  , mark: Nothing
  , markRing: []
  , globalMarkRing: []
  }

-- | Set mark at current point
setMark :: Ref MarkPointState -> Aff Unit
setMark stateRef = do
  state <- liftEffect $ Ref.read stateRef
  let newMark = state.point
  let newMarkRing = Array.take 16 (newMark : state.markRing)  -- Keep last 16 marks
  liftEffect $ Ref.write state
    { mark = Just newMark
    , markRing = newMarkRing
    } stateRef

-- | Set mark at position
setMarkAt :: Ref MarkPointState -> Position -> Aff Unit
setMarkAt stateRef position = do
  state <- liftEffect $ Ref.read stateRef
  let newMarkRing = Array.take 16 (position : state.markRing)
  liftEffect $ Ref.write state
    { mark = Just position
    , markRing = newMarkRing
    } stateRef

-- | Swap mark and point
swapMarkAndPoint :: Ref MarkPointState -> Aff Unit
swapMarkAndPoint stateRef = do
  state <- liftEffect $ Ref.read stateRef
  case state.mark of
    Nothing -> pure unit  -- No mark to swap
    Just mark -> do
      liftEffect $ Ref.write state
        { point = mark
        , mark = Just state.point
        } stateRef

-- | Pop mark from ring
popMark :: Ref MarkPointState -> Aff (Maybe Position)
popMark stateRef = do
  state <- liftEffect $ Ref.read stateRef
  case Array.head state.markRing of
    Nothing -> pure Nothing
    Just mark -> do
      let newRing = Array.drop 1 state.markRing
      liftEffect $ Ref.write state { markRing = newRing } stateRef
      pure (Just mark)

-- | Jump to mark
jumpToMark :: Ref MarkPointState -> Aff (Maybe Position)
jumpToMark stateRef = do
  state <- liftEffect $ Ref.read stateRef
  case state.mark of
    Nothing -> pure Nothing
    Just mark -> do
      liftEffect $ Ref.write state { point = mark } stateRef
      pure (Just mark)

-- | Get current region (between mark and point)
getCurrentRegion :: Ref MarkPointState -> Aff (Maybe Region)
getCurrentRegion stateRef = do
  state <- liftEffect $ Ref.read stateRef
  case state.mark of
    Nothing -> pure Nothing
    Just mark -> do
      let region = normalizeRegion state.point mark
      pure (Just region)

-- | Normalize region (ensure start < end)
normalizeRegion :: Position -> Position -> Region
normalizeRegion pos1 pos2 =
  if pos1.file == pos2.file then
    if pos1.line < pos2.line || (pos1.line == pos2.line && pos1.column <= pos2.column) then
      { start: pos1, end: pos2, file: pos1.file }
    else
      { start: pos2, end: pos1, file: pos1.file }
  else
    -- Different files - use point as start
    { start: pos1, end: pos2, file: pos1.file }

-- | Set global mark
setGlobalMark :: Ref MarkPointState -> String -> Position -> Aff Unit
setGlobalMark stateRef name position = do
  state <- liftEffect $ Ref.read stateRef
  let existingMark = Array.find (\(n /\ _) -> n == name) state.globalMarkRing
  let newGlobalRing = case existingMark of
        Nothing -> Array.take 16 ((name /\ position) : state.globalMarkRing)
        Just _ -> Array.map (\(n /\ p) -> if n == name then (n /\ position) else (n /\ p)) state.globalMarkRing
  liftEffect $ Ref.write state { globalMarkRing = newGlobalRing } stateRef

-- | Jump to global mark
jumpToGlobalMark :: Ref MarkPointState -> String -> Aff (Maybe Position)
jumpToGlobalMark stateRef name = do
  state <- liftEffect $ Ref.read stateRef
  case Array.find (\(n /\ _) -> n == name) state.globalMarkRing of
    Nothing -> pure Nothing
    Just (_ /\ position) -> do
      liftEffect $ Ref.write state { point = position } stateRef
      pure (Just position)

-- | List all marks
listMarks :: Ref MarkPointState -> Aff (Array (String /\ Position))
listMarks stateRef = do
  state <- liftEffect $ Ref.read stateRef
  pure state.globalMarkRing

-- | Clear mark
clearMark :: Ref MarkPointState -> Aff Unit
clearMark stateRef = do
  liftEffect $ Ref.modify_ (\s -> s { mark = Nothing }) stateRef

-- | Set point
setPoint :: Ref MarkPointState -> Position -> Aff Unit
setPoint stateRef position = do
  liftEffect $ Ref.modify_ (\s -> s { point = position }) stateRef

-- | Get point
getPoint :: Ref MarkPointState -> Aff Position
getPoint stateRef = do
  state <- liftEffect $ Ref.read stateRef
  pure state.point

-- | Get mark
getMark :: Ref MarkPointState -> Aff (Maybe Position)
getMark stateRef = do
  state <- liftEffect $ Ref.read stateRef
  pure state.mark
