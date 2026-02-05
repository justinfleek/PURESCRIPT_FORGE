{-|
Module      : Sidepanel.Components.EasterEggs.Tetris.TetrisRenderer
Description : Canvas rendering for Tetris game
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

Renders Tetris game state to canvas.
-}
module Sidepanel.Components.EasterEggs.Tetris.TetrisRenderer where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Sidepanel.Components.EasterEggs.Tetris.TetrisTypes
  ( GameState
  , Piece
  , CellState(..)
  , PieceType
  , gridWidth
  , gridHeight
  , getPieceColor
  , getPieceShape
  )

-- | Canvas context type (opaque)
foreign import data CanvasContext :: Type

-- | Get canvas context
foreign import getCanvasContext :: String -> Effect (Maybe CanvasContext)

-- | Clear canvas
foreign import clearCanvas :: CanvasContext -> Effect Unit

-- | Draw filled rectangle
foreign import drawRect :: CanvasContext -> Int -> Int -> Int -> Int -> String -> Effect Unit

-- | Draw rectangle outline
foreign import drawRectOutline :: CanvasContext -> Int -> Int -> Int -> Int -> String -> Effect Unit

-- | Draw text
foreign import drawText :: CanvasContext -> String -> Int -> Int -> String -> String -> Effect Unit

-- | Render game state
renderGame :: CanvasContext -> GameState -> Int -> Int -> Effect Unit
renderGame ctx state cellSize padding = do
  clearCanvas ctx
  
  -- Draw grid background
  drawGrid ctx cellSize padding
  
  -- Draw locked pieces on grid
  drawGridPieces ctx state.grid cellSize padding
  
  -- Draw current piece
  case state.currentPiece of
    Just piece -> drawPiece ctx piece cellSize padding
    Nothing -> pure unit
  
  -- Draw ghost piece (where piece will land)
  case state.currentPiece of
    Just piece -> drawGhostPiece ctx piece state.grid cellSize padding
    Nothing -> pure unit
  
  -- Draw UI (score, level, next piece)
  drawUI ctx state cellSize padding

-- | Draw game grid
drawGrid :: CanvasContext -> Int -> Int -> Effect Unit
drawGrid ctx cellSize padding = do
  let gridWidthPx = gridWidth * cellSize
  let gridHeightPx = gridHeight * cellSize
  
  -- Draw grid background
  drawRect ctx (padding - 1) (padding - 1) (gridWidthPx + 2) (gridHeightPx + 2) "#1a1a1a"
  
  -- Draw grid lines
  Array.range 0 gridWidth \x -> do
    let xPos = padding + (x * cellSize)
    drawRectOutline ctx xPos padding 1 gridHeightPx "#333"
  
  Array.range 0 gridHeight \y -> do
    let yPos = padding + (y * cellSize)
    drawRectOutline ctx padding yPos gridWidthPx 1 "#333"

-- | Draw pieces locked on grid
drawGridPieces :: CanvasContext -> Array (Array CellState) -> Int -> Int -> Effect Unit
drawGridPieces ctx grid cellSize padding = do
  Array.mapWithIndex grid \y row ->
    Array.mapWithIndex row \x cell ->
      case cell of
        Empty -> pure unit
        Filled pieceType -> do
          let xPos = padding + (x * cellSize)
          let yPos = padding + (y * cellSize)
          let color = getPieceColor pieceType
          drawRect ctx xPos yPos cellSize cellSize color
          drawRectOutline ctx xPos yPos cellSize cellSize "#000"

-- | Draw current piece
drawPiece :: CanvasContext -> Piece -> Int -> Int -> Effect Unit
drawPiece ctx piece cellSize padding = do
  let shape = piece.shape
  let pos = piece.position
  let color = getPieceColor piece.type_
  
  Array.mapWithIndex shape \rowIdx row ->
    Array.mapWithIndex row \colIdx cell ->
      if cell == 1 then do
        let xPos = padding + ((pos.x + colIdx) * cellSize)
        let yPos = padding + ((pos.y + rowIdx) * cellSize)
        drawRect ctx xPos yPos cellSize cellSize color
        drawRectOutline ctx xPos yPos cellSize cellSize "#fff"

-- | Draw ghost piece (where piece will land)
drawGhostPiece :: CanvasContext -> Piece -> Array (Array CellState) -> Int -> Int -> Effect Unit
drawGhostPiece ctx piece grid cellSize padding = do
  -- Find drop position
  let droppedPiece = dropToBottom grid piece
  let shape = droppedPiece.shape
  let pos = droppedPiece.position
  
  Array.mapWithIndex shape \rowIdx row ->
    Array.mapWithIndex row \colIdx cell ->
      if cell == 1 then do
        let xPos = padding + ((pos.x + colIdx) * cellSize)
        let yPos = padding + ((pos.y + rowIdx) * cellSize)
        -- Draw outline only
        drawRectOutline ctx xPos yPos cellSize cellSize "#888"
        drawRectOutline ctx (xPos + 1) (yPos + 1) (cellSize - 2) (cellSize - 2) "#888"

-- | Drop piece to bottom (simplified - would use logic from TetrisLogic)
dropToBottom :: Array (Array CellState) -> Piece -> Piece
dropToBottom grid piece = piece  -- Simplified - would calculate actual drop

-- | Draw UI (score, level, next piece)
drawUI :: CanvasContext -> GameState -> Int -> Int -> Effect Unit
drawUI ctx state cellSize padding = do
  let uiX = padding + (gridWidth * cellSize) + 20
  
  -- Score
  drawText ctx ("Score: " <> show state.score) uiX (padding + 20) "16px monospace" "#fff"
  
  -- Level
  drawText ctx ("Level: " <> show state.level) uiX (padding + 50) "16px monospace" "#fff"
  
  -- Lines cleared
  drawText ctx ("Lines: " <> show state.linesCleared) uiX (padding + 80) "16px monospace" "#fff"
  
  -- Next piece preview
  drawText ctx "Next:" uiX (padding + 120) "14px monospace" "#888"
  drawNextPiece ctx state.nextPiece uiX (padding + 140) cellSize
  
  -- Game over message
  if state.isGameOver then
    drawText ctx "GAME OVER" (padding + 50) (padding + (gridHeight * cellSize / 2)) "32px monospace" "#f00"
  else
    pure unit
  
  -- Paused message
  if state.isPaused then
    drawText ctx "PAUSED" (padding + 50) (padding + (gridHeight * cellSize / 2)) "32px monospace" "#ff0"
  else
    pure unit

-- | Draw next piece preview
drawNextPiece :: CanvasContext -> PieceType -> Int -> Int -> Int -> Effect Unit
drawNextPiece ctx pieceType x y cellSize = do
  let shape = getPieceShape pieceType 0
  let color = getPieceColor pieceType
  let previewSize = 4 * cellSize
  
  -- Draw preview background
  drawRect ctx x y previewSize previewSize "#1a1a1a"
  drawRectOutline ctx x y previewSize previewSize "#333"
  
  -- Draw piece
  Array.mapWithIndex shape \rowIdx row ->
    Array.mapWithIndex row \colIdx cell ->
      if cell == 1 then do
        let xPos = x + (colIdx * cellSize)
        let yPos = y + (rowIdx * cellSize)
        drawRect ctx xPos yPos cellSize cellSize color
        drawRectOutline ctx xPos yPos cellSize cellSize "#000"

