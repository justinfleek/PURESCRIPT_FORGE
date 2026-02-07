{-|
Module      : Sidepanel.Components.EasterEggs.Tetris.TetrisTypes
Description : Types for Tetris game
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

Core types for Tetris game logic.
-}
module Sidepanel.Components.EasterEggs.Tetris.TetrisTypes where

import Prelude

import Data.Array as Array

-- | Game grid dimensions
gridWidth :: Int
gridWidth = 10

gridHeight :: Int
gridHeight = 20

-- | Tetromino piece types
data PieceType
  = I  -- Straight line
  | O  -- Square
  | T  -- T-shape
  | S  -- S-shape
  | Z  -- Z-shape
  | J  -- J-shape
  | L  -- L-shape

derive instance eqPieceType :: Eq PieceType
derive instance ordPieceType :: Ord PieceType

-- | Cell state in grid
data CellState
  = Empty
  | Filled PieceType

derive instance eqCellState :: Eq CellState

-- | Position on grid
type Position =
  { x :: Int
  , y :: Int
  }

-- | Tetromino piece
type Piece =
  { type_ :: PieceType
  , position :: Position
  , rotation :: Int  -- 0-3 (0°, 90°, 180°, 270°)
  , shape :: Array (Array Int)  -- 4x4 grid representing piece shape
  }

-- | Game state
type GameState =
  { grid :: Array (Array CellState)  -- 20x10 grid
  , currentPiece :: Maybe Piece
  , nextPiece :: PieceType
  , heldPiece :: Maybe PieceType
  , hasHeldThisTurn :: Boolean
  , score :: Int
  , linesCleared :: Int
  , level :: Int
  , isGameOver :: Boolean
  , isPaused :: Boolean
  , dropTimer :: Number  -- Milliseconds until next drop
  , lastDropTime :: Number  -- Timestamp of last drop
  }

-- | Game action
data GameAction
  = MoveLeft
  | MoveRight
  | MoveDown
  | Rotate
  | HardDrop
  | Hold
  | Pause
  | Resume

-- | Game event
data GameEvent
  = LineCleared Int  -- Number of lines cleared
  | LevelUp Int  -- New level
  | GameOver
  | PieceLocked

-- | Initial game state
initialGameState :: GameState
initialGameState =
  { grid: Array.replicate gridHeight (Array.replicate gridWidth Empty)
  , currentPiece: Nothing
  , nextPiece: I
  , heldPiece: Nothing
  , hasHeldThisTurn: false
  , score: 0
  , linesCleared: 0
  , level: 1
  , isGameOver: false
  , isPaused: false
  , dropTimer: 1000.0  -- Start at 1 second per drop
  , lastDropTime: 0.0
  }

-- | Get piece shape for a given type and rotation
getPieceShape :: PieceType -> Int -> Array (Array Int)
getPieceShape type_ rotation = case type_ of
  I -> case rotation `mod` 2 of
    0 -> [[1,1,1,1], [0,0,0,0], [0,0,0,0], [0,0,0,0]]
    _ -> [[1,0,0,0], [1,0,0,0], [1,0,0,0], [1,0,0,0]]
  
  O -> [[1,1,0,0], [1,1,0,0], [0,0,0,0], [0,0,0,0]]
  
  T -> case rotation `mod` 4 of
    0 -> [[0,1,0,0], [1,1,1,0], [0,0,0,0], [0,0,0,0]]
    1 -> [[0,1,0,0], [0,1,1,0], [0,1,0,0], [0,0,0,0]]
    2 -> [[0,0,0,0], [1,1,1,0], [0,1,0,0], [0,0,0,0]]
    _ -> [[0,1,0,0], [1,1,0,0], [0,1,0,0], [0,0,0,0]]
  
  S -> case rotation `mod` 2 of
    0 -> [[0,1,1,0], [1,1,0,0], [0,0,0,0], [0,0,0,0]]
    _ -> [[0,1,0,0], [0,1,1,0], [0,0,1,0], [0,0,0,0]]
  
  Z -> case rotation `mod` 2 of
    0 -> [[1,1,0,0], [0,1,1,0], [0,0,0,0], [0,0,0,0]]
    _ -> [[0,0,1,0], [0,1,1,0], [0,1,0,0], [0,0,0,0]]
  
  J -> case rotation `mod` 4 of
    0 -> [[1,0,0,0], [1,1,1,0], [0,0,0,0], [0,0,0,0]]
    1 -> [[0,1,1,0], [0,1,0,0], [0,1,0,0], [0,0,0,0]]
    2 -> [[0,0,0,0], [1,1,1,0], [0,0,1,0], [0,0,0,0]]
    _ -> [[0,1,0,0], [0,1,0,0], [1,1,0,0], [0,0,0,0]]
  
  L -> case rotation `mod` 4 of
    0 -> [[0,0,1,0], [1,1,1,0], [0,0,0,0], [0,0,0,0]]
    1 -> [[0,1,0,0], [0,1,0,0], [0,1,1,0], [0,0,0,0]]
    2 -> [[0,0,0,0], [1,1,1,0], [1,0,0,0], [0,0,0,0]]
    _ -> [[1,1,0,0], [0,1,0,0], [0,1,0,0], [0,0,0,0]]

-- | Get color for piece type (for rendering)
getPieceColor :: PieceType -> String
getPieceColor = case _ of
  I -> "#00f0f0"  -- Cyan
  O -> "#f0f000"  -- Yellow
  T -> "#a000f0"  -- Purple
  S -> "#00f000"  -- Green
  Z -> "#f00000"  -- Red
  J -> "#0000f0"  -- Blue
  L -> "#f0a000"  -- Orange
