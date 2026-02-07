{-|
Module      : Sidepanel.Components.EasterEggs.Pong.Pong
Description : Main Pong game component
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

Main Halogen component for Pong game.
-}
module Sidepanel.Components.EasterEggs.Pong.Pong where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Class (liftEffect)
import Effect.Aff.Class (class MonadAff)
import Effect.Aff (Aff, delay, Milliseconds(..))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Sidepanel.Components.EasterEggs.Pong.PongTypes
  ( GameState
  , GameAction(..)
  , GameMode(..)
  , initialGameState
  )
import Sidepanel.Components.EasterEggs.Pong.PongLogic (updateGame, applyAction)
import Sidepanel.Components.EasterEggs.Pong.PongRenderer
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
  = GameEnded (Maybe Player)
  | GamePaused
  | GameResumed

-- | Import Player
import Sidepanel.Components.EasterEggs.Pong.PongTypes (Player)

-- | Component input
type Input = Unit

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \_ ->
      { gameState: initialGameState SinglePlayer
      , canvasContext: Nothing
      , animationFrameId: Nothing
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
    [ HP.class_ (H.ClassName "pong-game") ]
    [ HH.canvas
        [ HP.id "pong-canvas"
        , HP.width gameWidth
        , HP.height gameHeight
        , HP.class_ (H.ClassName "pong-canvas")
        ]
    , HH.div
        [ HP.class_ (H.ClassName "pong-controls") ]
        [ HH.button
            [ HP.class_ (H.ClassName "pong-btn")
            , HE.onClick \_ -> if state.gameState.isPaused then Resume else Pause
            ]
            [ HH.text (if state.gameState.isPaused then "Resume" else "Pause") ]
        , HH.button
            [ HP.class_ (H.ClassName "pong-btn")
            , HE.onClick \_ -> Restart
            ]
            [ HH.text "Restart" ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "pong-instructions") ]
        [ HH.p_ [ HH.text "W/S: Left Paddle" ]
        , HH.p_ [ HH.text "Arrow Up/Down: Right Paddle" ]
        , HH.p_ [ HH.text "P: Pause" ]
        ]
    ]

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Get canvas context
    ctx <- liftEffect $ getCanvasContext "pong-canvas"
    H.modify_ _ { canvasContext = ctx }
    
    -- Start game loop
    startGameLoop
  
  HandleKeyPress key -> do
    state <- H.get
    case key of
      "w" -> updateGameState (applyAction state.gameState MoveLeftPaddleUp)
      "W" -> updateGameState (applyAction state.gameState MoveLeftPaddleUp)
      "s" -> updateGameState (applyAction state.gameState MoveLeftPaddleDown)
      "S" -> updateGameState (applyAction state.gameState MoveLeftPaddleDown)
      "ArrowUp" -> updateGameState (applyAction state.gameState MoveRightPaddleUp)
      "ArrowDown" -> updateGameState (applyAction state.gameState MoveRightPaddleDown)
      "p" -> updateGameState (applyAction state.gameState Pause)
      "P" -> updateGameState (applyAction state.gameState Pause)
      _ -> pure unit
    
    renderCurrentState
  
  GameLoop -> do
    state <- H.get
    if state.gameState.isGameOver || state.gameState.isPaused then
      pure unit
    else do
      -- Update game state
      let updatedState = updateGame state.gameState
      H.modify_ _ { gameState = updatedState }
      
      if updatedState.isGameOver then
        H.raise (GameEnded updatedState.winner)
      else
        pure unit
      
      renderCurrentState
      -- Continue loop (~60 FPS)
      delay (Milliseconds 16.0)
      handleAction GameLoop
  
  Pause -> do
    updateGameState (applyAction (_.gameState <$> H.get) Pause)
    H.raise GamePaused
  
  Resume -> do
    state <- H.get
    updateGameState (applyAction state.gameState Resume)
    H.raise GameResumed
    startGameLoop
  
  Restart -> do
    state <- H.get
    H.modify_ _ { gameState = initialGameState state.gameState.gameMode }
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
      liftEffect $ renderGame ctx state.gameState

-- | Start game loop
startGameLoop :: forall m. MonadAff m => H.HalogenM State Action () Output m Unit
startGameLoop = do
  handleAction GameLoop

-- | Import game dimensions
import Sidepanel.Components.EasterEggs.Pong.PongTypes (gameWidth, gameHeight)

-- | Import getCanvasContext from Pong renderer
import Sidepanel.Components.EasterEggs.Pong.PongRenderer (getCanvasContext)
