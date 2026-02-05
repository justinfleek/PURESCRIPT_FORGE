{-|
Module      : Sidepanel.Components.EasterEggs.Pong.PongLogic
Description : Core Pong game logic
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

Game logic for Pong: physics, collision detection, scoring, AI.
-}
module Sidepanel.Components.EasterEggs.Pong.PongLogic where

import Prelude

import Data.Maybe (Maybe(..))
import Sidepanel.Components.EasterEggs.Pong.PongTypes
  ( GameState
  , GameAction(..)
  , Paddle
  , Ball
  , Player(..)
  , GameMode(..)
  , gameWidth
  , gameHeight
  )

-- | Update game state
updateGame :: GameState -> GameState
updateGame state = do
  if state.isPaused || state.isGameOver then
    state
  else do
    -- Move ball
    let updatedBall = moveBall state.ball
    
    -- Check collisions
    let ballAfterCollisions = checkCollisions updatedBall state.leftPaddle state.rightPaddle
    
    -- Check scoring
    let scoredState = checkScoring state ballAfterCollisions
    
    -- Move AI paddle (if single player)
    let finalState = if scoredState.gameMode == SinglePlayer then
          updateAIPaddle scoredState
        else
          scoredState
    
    -- Check game over (first to 11)
    checkGameOver finalState

-- | Move ball
moveBall :: Ball -> Ball
moveBall ball = do
  ball
    { x = ball.x + ball.velocityX
    , y = ball.y + ball.velocityY
    }

-- | Check collisions with paddles and walls
checkCollisions :: Ball -> Paddle -> Paddle -> Ball
checkCollisions ball leftPaddle rightPaddle = do
  let ballAfterWalls = checkWallCollisions ball
  let ballAfterLeft = checkPaddleCollision ballAfterWalls leftPaddle true
  checkPaddleCollision ballAfterLeft rightPaddle false

-- | Check wall collisions (top/bottom)
checkWallCollisions :: Ball -> Ball
checkWallCollisions ball = do
  if ball.y - ball.radius <= 0.0 || ball.y + ball.radius >= Number.fromInt gameHeight then
    ball { velocityY = -ball.velocityY }
  else
    ball

-- | Check paddle collision
checkPaddleCollision :: Ball -> Paddle -> Boolean -> Ball
checkPaddleCollision ball paddle isLeft = do
  let ballLeft = ball.x - ball.radius
  let ballRight = ball.x + ball.radius
  let ballTop = ball.y - ball.radius
  let ballBottom = ball.y + ball.radius
  
  let paddleLeft = paddle.x
  let paddleRight = paddle.x + paddle.width
  let paddleTop = paddle.y
  let paddleBottom = paddle.y + paddle.height
  
  let collides = if isLeft then
        ballLeft <= paddleRight && ballRight >= paddleLeft &&
        ballTop <= paddleBottom && ballBottom >= paddleTop
      else
        ballRight >= paddleLeft && ballLeft <= paddleRight &&
        ballTop <= paddleBottom && ballBottom >= paddleTop
  
  if collides then
    -- Reverse X velocity and add slight angle based on where ball hit paddle
    let hitPosition = (ball.y - paddle.y) / paddle.height  -- 0.0 to 1.0
    let angle = (hitPosition - 0.5) * 2.0  -- -1.0 to 1.0
    let newVelocityX = if isLeft then abs ball.velocityX else -abs ball.velocityX
    let newVelocityY = ball.velocityY + (angle * 2.0)
    ball
      { velocityX = newVelocityX
      , velocityY = newVelocityY
      }
  else
    ball

-- | Check scoring (ball goes off left or right edge)
checkScoring :: GameState -> Ball -> GameState
checkScoring state ball = do
  if ball.x < 0.0 then
    -- Right player scores
    state
      { rightScore = state.rightScore + 1
      , ball = resetBall state.ball false
      }
  else if ball.x > Number.fromInt gameWidth then
    -- Left player scores
    state
      { leftScore = state.leftScore + 1
      , ball = resetBall state.ball true
      }
  else
    state { ball = ball }

-- | Reset ball to center
resetBall :: Ball -> Boolean -> Ball
resetBall ball goLeft = do
  ball
    { x = Number.fromInt (gameWidth / 2)
    , y = Number.fromInt (gameHeight / 2)
    , velocityX = if goLeft then -3.0 else 3.0
    , velocityY = 3.0
    }

-- | Update AI paddle (simple follow-ball AI)
updateAIPaddle :: GameState -> GameState
updateAIPaddle state = do
  let aiPaddle = state.rightPaddle
  let ballY = state.ball.y
  let paddleCenter = aiPaddle.y + (aiPaddle.height / 2.0)
  
  let targetY = ballY - (aiPaddle.height / 2.0)
  let newY = if paddleCenter < ballY - 5.0 then
        min targetY (aiPaddle.y + aiPaddle.speed)
      else if paddleCenter > ballY + 5.0 then
        max targetY (aiPaddle.y - aiPaddle.speed)
      else
        aiPaddle.y
  
  -- Keep paddle in bounds
  let clampedY = max 0.0 (min (Number.fromInt gameHeight - aiPaddle.height) newY)
  
  state { rightPaddle = aiPaddle { y = clampedY } }

-- | Check if game is over
checkGameOver :: GameState -> GameState
checkGameOver state = do
  if state.leftScore >= 11 then
    state { isGameOver = true, winner = Just LeftPlayer }
  else if state.rightScore >= 11 then
    state { isGameOver = true, winner = Just RightPlayer }
  else
    state

-- | Apply game action
applyAction :: GameState -> GameAction -> GameState
applyAction state = case _ of
  MoveLeftPaddleUp -> movePaddle state true (-1.0)
  MoveLeftPaddleDown -> movePaddle state true 1.0
  MoveRightPaddleUp -> movePaddle state false (-1.0)
  MoveRightPaddleDown -> movePaddle state false 1.0
  Pause -> state { isPaused = true }
  Resume -> state { isPaused = false }
  Restart -> initialGameState state.gameMode

-- | Move paddle
movePaddle :: GameState -> Boolean -> Number -> GameState
movePaddle state isLeft direction = do
  let paddle = if isLeft then state.leftPaddle else state.rightPaddle
  let newY = paddle.y + (direction * paddle.speed)
  let clampedY = max 0.0 (min (Number.fromInt gameHeight - paddle.height) newY)
  let updatedPaddle = paddle { y = clampedY }
  
  if isLeft then
    state { leftPaddle = updatedPaddle }
  else
    state { rightPaddle = updatedPaddle }

-- | Import abs
import Data.Number (abs)
