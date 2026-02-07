{-|
Module      : Sidepanel.Components.EasterEggs.Pong.PongTypes
Description : Types for Pong game
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

Core types for Pong game logic.
-}
module Sidepanel.Components.EasterEggs.Pong.PongTypes where

import Prelude

-- | Game dimensions
gameWidth :: Int
gameWidth = 800

gameHeight :: Int
gameHeight = 600

-- | Paddle position
type Paddle =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  , speed :: Number
  }

-- | Ball state
type Ball =
  { x :: Number
  , y :: Number
  , radius :: Number
  , velocityX :: Number
  , velocityY :: Number
  , speed :: Number
  }

-- | Game state
type GameState =
  { leftPaddle :: Paddle
  , rightPaddle :: Paddle
  , ball :: Ball
  , leftScore :: Int
  , rightScore :: Int
  , isPaused :: Boolean
  , isGameOver :: Boolean
  , winner :: Maybe Player
  , gameMode :: GameMode
  }

-- | Player
data Player
  = LeftPlayer
  | RightPlayer

derive instance eqPlayer :: Eq Player

-- | Game mode
data GameMode
  = SinglePlayer  -- Play against AI
  | TwoPlayer     -- Play against friend

derive instance eqGameMode :: Eq GameMode

-- | Game action
data GameAction
  = MoveLeftPaddleUp
  | MoveLeftPaddleDown
  | MoveRightPaddleUp
  | MoveRightPaddleDown
  | Pause
  | Resume
  | Restart

-- | Initial game state
initialGameState :: GameMode -> GameState
initialGameState mode =
  { leftPaddle:
      { x: 20.0
      , y: Number.fromInt (gameHeight / 2 - 50)
      , width: 10.0
      , height: 100.0
      , speed: 5.0
      }
  , rightPaddle:
      { x: Number.fromInt (gameWidth - 30)
      , y: Number.fromInt (gameHeight / 2 - 50)
      , width: 10.0
      , height: 100.0
      , speed: 5.0
      }
  , ball:
      { x: Number.fromInt (gameWidth / 2)
      , y: Number.fromInt (gameHeight / 2)
      , radius: 10.0
      , velocityX: 3.0
      , velocityY: 3.0
      , speed: 3.0
      }
  , leftScore: 0
  , rightScore: 0
  , isPaused: false
  , isGameOver: false
  , winner: Nothing
  , gameMode: mode
  }
