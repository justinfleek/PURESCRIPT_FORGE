{-|
Module      : Sidepanel.Components.EasterEggs.Tetris.TetrisLogic
Description : Core Tetris game logic
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

Game logic for Tetris: piece movement, rotation, collision detection, line clearing.
-}
module Sidepanel.Components.EasterEggs.Tetris.TetrisLogic where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Traversable (traverse)
import Effect.Random (randomInt)
import Sidepanel.Components.EasterEggs.Tetris.TetrisTypes
  ( GameState
  , GameAction
  , GameEvent
  , Piece
  , PieceType(..)
  , CellState(..)
  , Position
  , gridWidth
  , gridHeight
  , getPieceShape
  , initialGameState
  )

-- | Apply game action to state
applyAction :: GameState -> GameAction -> GameState
applyAction state = case _ of
  MoveLeft -> tryMovePiece state { x: -1, y: 0 }
  MoveRight -> tryMovePiece state { x: 1, y: 0 }
  MoveDown -> tryMovePiece state { x: 0, y: 1 }
  Rotate -> tryRotatePiece state
  HardDrop -> hardDropPiece state
  Hold -> holdPiece state
  Pause -> state { isPaused = true }
  Resume -> state { isPaused = false }

-- | Try to move piece
tryMovePiece :: GameState -> Position -> GameState
tryMovePiece state offset = case state.currentPiece of
  Nothing -> state
  Just piece -> do
    let newPos = { x: piece.position.x + offset.x, y: piece.position.y + offset.y }
    let newPiece = piece { position = newPos }
    if isValidPosition state.grid newPiece then
      state { currentPiece = Just newPiece }
    else
      state

-- | Try to rotate piece
tryRotatePiece :: GameState -> GameState
tryRotatePiece state = case state.currentPiece of
  Nothing -> state
  Just piece -> do
    let newRotation = (piece.rotation + 1) `mod` 4
    let newShape = getPieceShape piece.type_ newRotation
    let newPiece = piece { rotation = newRotation, shape = newShape }
    if isValidPosition state.grid newPiece then
      state { currentPiece = Just newPiece }
    else
      -- Try wall kicks (shift left/right if rotation fails)
      let kickedLeft = newPiece { position = { x: piece.position.x - 1, y: piece.position.y } }
      let kickedRight = newPiece { position = { x: piece.position.x + 1, y: piece.position.y } }
      if isValidPosition state.grid kickedLeft then
        state { currentPiece = Just kickedLeft }
      else if isValidPosition state.grid kickedRight then
        state { currentPiece = Just kickedRight }
      else
        state

-- | Hard drop piece to bottom
hardDropPiece :: GameState -> GameState
hardDropPiece state = case state.currentPiece of
  Nothing -> state
  Just piece -> do
    let droppedPiece = dropToBottom state.grid piece
    let newState = lockPiece state droppedPiece
    newState

-- | Drop piece to lowest valid position
dropToBottom :: Array (Array CellState) -> Piece -> Piece
dropToBottom grid piece = do
  let maxDrop = findMaxDrop grid piece
  piece { position = { x: piece.position.x, y: piece.position.y + maxDrop } }

-- | Find maximum drop distance
findMaxDrop :: Array (Array CellState) -> Piece -> Int
findMaxDrop grid piece = do
  let testDrop n = isValidPosition grid (piece { position = { x: piece.position.x, y: piece.position.y + n } })
  let maxY = gridHeight - 1
  let maxDrop = Array.findLastIndex (\n -> testDrop n) (Array.range 0 maxY)
  fromMaybe 0 maxDrop

-- | Check if piece position is valid
isValidPosition :: Array (Array CellState) -> Piece -> Boolean
isValidPosition grid piece = do
  let shape = piece.shape
  let pos = piece.position
  
  -- Check each cell of piece shape
  Array.allWithIndex shape \rowIdx row ->
    Array.allWithIndex row \colIdx cell ->
      if cell == 1 then do
        let gridX = pos.x + colIdx
        let gridY = pos.y + rowIdx
        
        -- Check bounds
        if gridX < 0 || gridX >= gridWidth || gridY < 0 || gridY >= gridHeight then
          false
        else do
          -- Check collision with existing blocks
          case Array.index grid gridY of
            Nothing -> false
            Just row -> case Array.index row gridX of
              Nothing -> false
              Just cellState -> cellState == Empty
      else
        true

-- | Lock piece to grid
lockPiece :: GameState -> Piece -> GameState
lockPiece state piece = do
  let newGrid = placePieceOnGrid state.grid piece
  let cleared = clearLines newGrid
  let linesCleared = Array.length cleared.linesToClear
  let newScore = calculateScore state.score linesCleared state.level
  let newLevel = if linesCleared > 0 then calculateLevel (state.linesCleared + linesCleared) else state.level
  let newDropTimer = calculateDropTimer newLevel
  
  -- Spawn next piece
  let nextPiece = spawnPiece state.nextPiece (newScore + state.linesCleared + linesCleared)
  let isGameOver = case nextPiece.currentPiece of
    Just p -> not (isValidPosition cleared.grid p)
    Nothing -> true

  { grid: cleared.grid
  , currentPiece: nextPiece.currentPiece
  , nextPiece: nextPiece.nextPiece
  , heldPiece: state.heldPiece
  , hasHeldThisTurn: false
  , score: newScore
  , linesCleared: state.linesCleared + linesCleared
  , level: newLevel
  , isGameOver: isGameOver
  , isPaused: state.isPaused
  , dropTimer: newDropTimer
  , lastDropTime: state.lastDropTime
  }

-- | Place piece on grid
placePieceOnGrid :: Array (Array CellState) -> Piece -> Array (Array CellState)
placePieceOnGrid grid piece = do
  let shape = piece.shape
  let pos = piece.position
  
  Array.mapWithIndex grid \rowIdx row ->
    Array.mapWithIndex row \colIdx cell ->
      let shapeRowIdx = rowIdx - pos.y
      let shapeColIdx = colIdx - pos.x
      in if shapeRowIdx >= 0 && shapeRowIdx < 4 && shapeColIdx >= 0 && shapeColIdx < 4 then
        case Array.index shape shapeRowIdx of
          Nothing -> cell
          Just shapeRow -> case Array.index shapeRow shapeColIdx of
            Nothing -> cell
            Just shapeCell -> if shapeCell == 1 then Filled piece.type_ else cell
      else
        cell

-- | Clear completed lines
clearLines :: Array (Array CellState) -> { grid :: Array (Array CellState), linesToClear :: Array Int }
clearLines grid = do
  let linesToClear = Array.findIndices isLineFull grid
  let clearedGrid = Array.foldl removeLine grid linesToClear
  { grid: clearedGrid, linesToClear: linesToClear }

-- | Check if line is full
isLineFull :: Array CellState -> Boolean
isLineFull line = Array.all (_ /= Empty) line

-- | Remove line and add empty line at top
removeLine :: Array (Array CellState) -> Int -> Array (Array CellState)
removeLine grid lineIdx = do
  let before = Array.take lineIdx grid
  let after = Array.drop (lineIdx + 1) grid
  let emptyLine = Array.replicate gridWidth Empty
  before <> after <> [emptyLine]

-- | Calculate score
calculateScore :: Int -> Int -> Int -> Int
calculateScore currentScore lines level = do
  let baseScore = case lines of
    1 -> 100
    2 -> 300
    3 -> 500
    4 -> 800
    _ -> 0
  currentScore + (baseScore * level)

-- | Calculate level from lines cleared
calculateLevel :: Int -> Int
calculateLevel linesCleared = (linesCleared / 10) + 1

-- | Calculate drop timer based on level
calculateDropTimer :: Int -> Number
calculateDropTimer level = do
  let baseTimer = 1000.0
  let levelSpeed = Number.fromInt level * 50.0
  max 50.0 (baseTimer - levelSpeed)  -- Minimum 50ms

-- | Hold current piece: swap with held piece or store if none held
holdPiece :: GameState -> GameState
holdPiece state =
  if state.hasHeldThisTurn then state  -- Can only hold once per piece
  else case state.currentPiece of
    Nothing -> state
    Just piece -> case state.heldPiece of
      Nothing ->
        -- No held piece: store current, spawn next
        let spawned = spawnPiece state.nextPiece (state.score + state.linesCleared)
        in state
          { currentPiece = spawned.currentPiece
          , nextPiece = spawned.nextPiece
          , heldPiece = Just piece.type_
          , hasHeldThisTurn = true
          }
      Just heldType ->
        -- Swap current with held
        let newPiece = { type_: heldType, position: { x: 3, y: 0 }, rotation: 0, shape: getPieceShape heldType 0 }
        in state
          { currentPiece = Just newPiece
          , heldPiece = Just piece.type_
          , hasHeldThisTurn = true
          }

-- | Spawn new piece
spawnPiece :: PieceType -> Int -> { currentPiece :: Maybe Piece, nextPiece :: PieceType }
spawnPiece currentType seed = do
  let nextType = randomPieceType seed
  let piece = { type_: currentType, position: { x: 3, y: 0 }, rotation: 0, shape: getPieceShape currentType 0 }
  { currentPiece: Just piece, nextPiece: nextType }

-- | Generate piece type from seed using linear congruential generator
-- | Uses score + linesCleared as entropy source for deterministic selection
randomPieceType :: Int -> PieceType
randomPieceType seed =
  let pieceTypes = [I, O, T, S, Z, J, L]
      -- LCG parameters (Numerical Recipes)
      hash = abs ((seed * 1103515245 + 12345) `mod` 7)
  in fromMaybe I (Array.index pieceTypes hash)

-- | Update game state (handle automatic drops)
updateGame :: Number -> GameState -> GameState
updateGame currentTime state = do
  if state.isPaused || state.isGameOver then
    state
  else do
    let timeSinceLastDrop = currentTime - state.lastDropTime
    if timeSinceLastDrop >= state.dropTimer then
      let movedState = applyAction state MoveDown
      case movedState.currentPiece of
        Nothing -> movedState  -- Piece was locked
        Just piece -> do
          -- Check if piece can still move down
          let testPiece = piece { position = { x: piece.position.x, y: piece.position.y + 1 } }
          if isValidPosition movedState.grid testPiece then
            movedState { lastDropTime = currentTime }
          else
            -- Lock piece
            lockPiece movedState piece { lastDropTime = currentTime }
    else
      state
