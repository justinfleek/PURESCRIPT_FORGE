{-|
Module      : Sidepanel.Components.EasterEggs.Tetris.Tetris
Description : Main Tetris game component
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

Main Halogen component for Tetris game.
-}
module Sidepanel.Components.EasterEggs.Tetris.Tetris where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Class (liftEffect)
import Effect.Aff.Class (class MonadAff)
import Effect.Aff (Aff, delay, Milliseconds(..))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect (Effect)
import Sidepanel.Components.EasterEggs.Tetris.TetrisTypes
  ( GameState
  , GameAction(..)
  , initialGameState
  , PieceType(..)
  )
import Sidepanel.Components.EasterEggs.Tetris.TetrisLogic
  ( applyAction
  , updateGame
  , spawnPiece
  )
import Sidepanel.Components.EasterEggs.Tetris.TetrisRenderer
  ( CanvasContext
  , getCanvasContext
  , renderGame
  )
import Sidepanel.Components.EasterEggs.Tetris.TetrisFFI (getCurrentTime) as FFI

-- | Component state
type State =
  { gameState :: GameState
  , canvasContext :: Maybe CanvasContext
  , animationFrameId :: Maybe Int
  , cellSize :: Int
  , padding :: Int
  }

-- | Component actions
data Action
  = Initialize
  | HandleKeyPress String
  | GameLoop
  | Pause
  | Resume
  | Restart

-- | Component output
data Output
  = GameEnded Int  -- Final score
  | GamePaused
  | GameResumed

-- | Component input
type Input = Unit

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \_ ->
      { gameState: initialGameState
      , canvasContext: Nothing
      , animationFrameId: Nothing
      , cellSize: 25
      , padding: 10
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
    [ HP.class_ (H.ClassName "tetris-game") ]
    [ HH.canvas
        [ HP.id "tetris-canvas"
        , HP.width 400
        , HP.height 600
        , HP.class_ (H.ClassName "tetris-canvas")
        ]
    , HH.div
        [ HP.class_ (H.ClassName "tetris-controls") ]
        [ HH.button
            [ HP.class_ (H.ClassName "tetris-btn")
            , HE.onClick \_ -> if state.gameState.isPaused then Resume else Pause
            ]
            [ HH.text (if state.gameState.isPaused then "Resume" else "Pause") ]
        , HH.button
            [ HP.class_ (H.ClassName "tetris-btn")
            , HE.onClick \_ -> Restart
            ]
            [ HH.text "Restart" ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "tetris-instructions") ]
        [ HH.p_ [ HH.text "Arrow Keys: Move/Rotate" ]
        , HH.p_ [ HH.text "Space: Hard Drop" ]
        , HH.p_ [ HH.text "P: Pause" ]
        ]
    ]

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Get canvas context
    ctx <- liftEffect $ getCanvasContext "tetris-canvas"
    H.modify_ _ { canvasContext = ctx }
    
    -- Spawn initial piece
    state <- H.get
    let newPiece = spawnPiece I
    H.modify_ \s -> s
      { gameState = s.gameState
          { currentPiece = newPiece.currentPiece
          , nextPiece = newPiece.nextPiece
          }
      }
    
    -- Start game loop
    startGameLoop
  
  HandleKeyPress key -> do
    state <- H.get
    case key of
      "ArrowLeft" -> updateGameState (applyAction state.gameState MoveLeft)
      "ArrowRight" -> updateGameState (applyAction state.gameState MoveRight)
      "ArrowDown" -> updateGameState (applyAction state.gameState MoveDown)
      "ArrowUp" -> updateGameState (applyAction state.gameState Rotate)
      " " -> updateGameState (applyAction state.gameState HardDrop)
      "p" -> updateGameState (applyAction state.gameState Pause)
      "P" -> updateGameState (applyAction state.gameState Pause)
      _ -> pure unit
    
    renderCurrentState
  
  GameLoop -> do
    state <- H.get
    if state.gameState.isGameOver || state.gameState.isPaused then
      pure unit
    else do
      currentTime <- liftEffect FFI.getCurrentTime
      let updatedState = updateGame (Number.fromInt currentTime) state.gameState
      H.modify_ _ { gameState = updatedState }
      
      if updatedState.isGameOver then
        H.raise (GameEnded updatedState.score)
      else
        pure unit
      
      renderCurrentState
      -- Continue loop
      delay (Milliseconds 16.0)  -- ~60 FPS
      handleAction GameLoop
  
  Pause -> do
    state <- H.get
    updateGameState (applyAction state.gameState Pause)
    H.raise GamePaused
  
  Resume -> do
    state <- H.get
    updateGameState (applyAction state.gameState Resume)
    H.raise GameResumed
    startGameLoop
  
  Restart -> do
    H.modify_ _ { gameState = initialGameState }
    -- Spawn initial piece
    state <- H.get
    let newPiece = spawnPiece I
    H.modify_ \s -> s
      { gameState = s.gameState
          { currentPiece = newPiece.currentPiece
          , nextPiece = newPiece.nextPiece
          }
      }
    renderCurrentState
    startGameLoop

-- | Update game state
updateGameState :: forall m. MonadAff m => GameState -> H.HalogenM State Action () Output m Unit
updateGameState newState = do
  H.modify_ _ { gameState = newState }

-- | Render current state to canvas
renderCurrentState :: forall m. MonadAff m => H.HalogenM State Action () Output m Unit
renderCurrentState = do
  state <- H.get
  case state.canvasContext of
    Nothing -> pure unit
    Just ctx -> do
      liftEffect $ renderGame ctx state.gameState state.cellSize state.padding

-- | Start game loop
startGameLoop :: forall m. MonadAff m => H.HalogenM State Action () Output m Unit
startGameLoop = do
  handleAction GameLoop
