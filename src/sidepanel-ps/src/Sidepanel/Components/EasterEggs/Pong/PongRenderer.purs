{-|
Module      : Sidepanel.Components.EasterEggs.Pong.PongRenderer
Description : Canvas rendering for Pong game
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

Renders Pong game state to canvas.
-}
module Sidepanel.Components.EasterEggs.Pong.PongRenderer where

import Prelude

import Effect (Effect)
import Sidepanel.Components.EasterEggs.Pong.PongTypes
  ( GameState
  , Paddle
  , Ball
  , Player(..)
  , gameWidth
  , gameHeight
  )
-- | Canvas context type (reuse from Tetris)
foreign import data CanvasContext :: Type

-- | Get canvas context
foreign import getCanvasContext :: String -> Effect (Maybe CanvasContext)

-- | Clear canvas
foreign import clearCanvas :: CanvasContext -> Effect Unit

-- | Draw filled rectangle
foreign import drawRect :: CanvasContext -> Int -> Int -> Int -> Int -> String -> Effect Unit

-- | Draw text
foreign import drawText :: CanvasContext -> String -> Int -> Int -> String -> String -> Effect Unit

-- | Render game state
renderGame :: CanvasContext -> GameState -> Effect Unit
renderGame ctx state = do
  clearCanvas ctx
  
  -- Draw background
  drawRect ctx 0 0 gameWidth gameHeight "#000"
  
  -- Draw center line
  drawCenterLine ctx
  
  -- Draw paddles
  drawPaddle ctx state.leftPaddle "#fff"
  drawPaddle ctx state.rightPaddle "#fff"
  
  -- Draw ball
  drawBall ctx state.ball
  
  -- Draw scores
  drawScore ctx state.leftScore state.rightScore
  
  -- Draw UI messages
  if state.isGameOver then
    drawGameOver ctx state.winner
  else if state.isPaused then
    drawPaused ctx
  else
    pure unit

-- | Draw center line (dashed)
drawCenterLine :: CanvasContext -> Effect Unit
drawCenterLine ctx = do
  let centerX = gameWidth / 2
  let dashHeight = 20
  let gap = 10
  let numDashes = gameHeight / (dashHeight + gap)
  
  Array.range 0 (floor numDashes) \i -> do
    let y = i * (dashHeight + gap)
    if y < gameHeight then
      drawRect ctx centerX y 2 dashHeight "#666"
    else
      pure unit

-- | Draw paddle
drawPaddle :: CanvasContext -> Paddle -> String -> Effect Unit
drawPaddle ctx paddle color = do
  drawRect ctx (floor paddle.x) (floor paddle.y) 
    (floor paddle.width) (floor paddle.height) color

-- | Draw ball
drawBall :: CanvasContext -> Ball -> Effect Unit
drawBall ctx ball = do
  -- Draw circle (using filled rect as approximation)
  let x = floor (ball.x - ball.radius)
  let y = floor (ball.y - ball.radius)
  let size = floor (ball.radius * 2.0)
  drawRect ctx x y size size "#fff"

-- | Draw score
drawScore :: CanvasContext -> Int -> Int -> Effect Unit
drawScore ctx leftScore rightScore = do
  let centerX = gameWidth / 2
  drawText ctx (show leftScore) (centerX - 100) 50 "48px monospace" "#fff"
  drawText ctx (show rightScore) (centerX + 100) 50 "48px monospace" "#fff"

-- | Draw game over message
drawGameOver :: CanvasContext -> Maybe Player -> Effect Unit
drawGameOver ctx winner = do
  let message = case winner of
    Just LeftPlayer -> "LEFT PLAYER WINS!"
    Just RightPlayer -> "RIGHT PLAYER WINS!"
    Nothing -> "GAME OVER"
  drawText ctx message (gameWidth / 2 - 150) (gameHeight / 2) "32px monospace" "#ff0"

-- | Draw paused message
drawPaused :: CanvasContext -> Effect Unit
drawPaused ctx = do
  drawText ctx "PAUSED" (gameWidth / 2 - 80) (gameHeight / 2) "32px monospace" "#ff0"

-- | Import utilities
import Data.Array as Array
import Math (floor)
