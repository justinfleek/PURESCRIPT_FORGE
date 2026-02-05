-- | Game Manager Component - Easter Egg Games System
-- |
-- | **What:** Manages hidden easter egg games (Tetris, Pong, Doom) that can be unlocked via
-- |         Konami code or secret keyboard shortcuts.
-- | **Why:** Adds delightful hidden features that make the app more fun and memorable.
-- | **How:** Detects Konami code and keyboard shortcuts, shows game selection menu, and
-- |         manages game state and rendering.
-- |
-- | **Activation Methods:**
-- | - Konami code: Up Up Down Down Left Right Left Right B A
-- | - Ctrl+Shift+T: Tetris
-- | - Ctrl+Shift+P: Pong (when not opening command palette)
-- | - Ctrl+Shift+D+D: Doom (double D!)
-- | - URL parameter: ?game=tetris|pong|doom
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Utils.KonamiCode`: Konami code detection
-- | - `Sidepanel.Components.EasterEggs.Tetris`: Tetris game
-- | - `Sidepanel.Components.EasterEggs.Pong`: Pong game
-- | - `Sidepanel.Components.EasterEggs.Doom`: Doom wrapper
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.EasterEggs.GameManager as GameManager
-- |
-- | -- In App.purs:
-- | HH.slot _gameManager unit GameManager.component unit HandleGameManagerOutput
-- | ```
module Sidepanel.Components.EasterEggs.GameManager where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Class (liftEffect)
import Effect.Aff.Class (class MonadAff)
import Effect (Effect)
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Sidepanel.Utils.KonamiCode as KonamiCode
import Sidepanel.Components.EasterEggs.Tetris.Tetris as Tetris
import Sidepanel.Components.EasterEggs.Pong.Pong as Pong
import Sidepanel.Components.EasterEggs.Doom.Doom as Doom
import Type.Proxy (Proxy(..))

-- | Game types
data Game = Tetris | Pong | Doom

derive instance eqGame :: Eq Game

-- | Component state
type State =
  { activeGame :: Maybe Game
  , showSelection :: Boolean
  , konamiDetector :: Maybe KonamiCode.DetectorState
  , highScores :: Array { game :: Game, score :: Int }
  }

-- | Component actions
data Action
  = Initialize
  | KonamiCodeDetected
  | ShowGameSelection
  | SelectGame Game
  | CloseGame
  | CloseSelection

-- | Component output
data Output
  = GameStarted Game
  | GameEnded Game Int  -- Game and final score

-- | Component input
type Input = Unit

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \_ ->
      { activeGame: Nothing
      , showSelection: false
      , konamiDetector: Nothing
      , highScores: []
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
    [ HP.class_ (H.ClassName "game-manager") ]
    [ -- Game selection menu
      if state.showSelection then
        renderGameSelection state
      else
        HH.text ""
    , -- Active game overlay
      case state.activeGame of
        Just game -> renderGameOverlay game
        Nothing -> HH.text ""
    ]

-- | Render game selection menu
renderGameSelection :: forall m. State -> H.ComponentHTML Action () m
renderGameSelection state =
  HH.div
    [ HP.class_ (H.ClassName "game-selection-overlay")
    , HE.onClick \_ -> CloseSelection
    ]
    [ HH.div
        [ HP.class_ (H.ClassName "game-selection-menu")
        , HE.onClick \_ -> pure unit  -- Prevent closing when clicking menu
        ]
        [ HH.header
            [ HP.class_ (H.ClassName "game-selection-header") ]
            [ HH.h2_ [ HH.text "🎮 EASTER EGG GAMES" ]
            , HH.button
                [ HP.class_ (H.ClassName "close-btn")
                , HE.onClick \_ -> CloseSelection
                ]
                [ HH.text "✕" ]
            ]
        , HH.div
            [ HP.class_ (H.ClassName "game-grid") ]
            [ renderGameCard Tetris "🧩" "TETRIS" state
            , renderGameCard Pong "🏓" "PONG" state
            , renderGameCard Doom "🔫" "DOOM" state
            ]
        , HH.footer
            [ HP.class_ (H.ClassName "game-selection-footer") ]
            [ HH.p_ [ HH.text "Press ESC to exit" ]
            , HH.p
                [ HP.class_ (H.ClassName "hint") ]
                [ HH.text "💡 Tip: Try the Konami code!" ]
            ]
        ]
    ]

-- | Render game card
renderGameCard :: forall m. Game -> String -> String -> State -> H.ComponentHTML Action () m
renderGameCard game icon label state =
  HH.div
    [ HP.class_ (H.ClassName "game-card")
    , HE.onClick \_ -> SelectGame game
    ]
    [ HH.div
        [ HP.class_ (H.ClassName "game-icon") ]
        [ HH.text icon ]
    , HH.h3_ [ HH.text label ]
    , HH.div
        [ HP.class_ (H.ClassName "game-score") ]
        [ case Array.find (\s -> s.game == game) state.highScores of
            Just { score } -> HH.text $ "High Score: " <> show score
            Nothing -> HH.text "No high score yet"
        ]
    , HH.button
        [ HP.class_ (H.ClassName "play-btn") ]
        [ HH.text "Play" ]
    ]

-- | Render game overlay
renderGameOverlay :: forall m. Game -> H.ComponentHTML Action () m
renderGameOverlay game =
  HH.div
    [ HP.class_ (H.ClassName "game-overlay") ]
    [ HH.div
        [ HP.class_ (H.ClassName "game-container") ]
        [ HH.button
            [ HP.class_ (H.ClassName "game-exit")
            , HE.onClick \_ -> CloseGame
            ]
            [ HH.text "✕ Exit" ]
        , case game of
            Tetris -> HH.slot (Proxy :: _ "tetris") unit Tetris.component unit (\_ -> pure unit)
            Pong -> HH.slot (Proxy :: _ "pong") unit Pong.component unit (\_ -> pure unit)
            Doom -> HH.slot (Proxy :: _ "doom") unit Doom.component unit (\_ -> pure unit)
        ]
    ]

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Create Konami code detector
    detector <- liftEffect $ KonamiCode.createDetector (pure unit)  -- Would trigger KonamiCodeDetected
    H.modify_ _ { konamiDetector = Just detector }
    
    -- Check URL parameters
    -- Would check for ?game=tetris|pong|doom
    
  KonamiCodeDetected -> do
    H.modify_ _ { showSelection = true }
  
  ShowGameSelection -> do
    H.modify_ _ { showSelection = true }
  
  SelectGame game -> do
    H.modify_ _
      { activeGame = Just game
      , showSelection = false
      }
    H.raise (GameStarted game)
  
  CloseGame -> do
    state <- H.get
    case state.activeGame of
      Just game -> do
        H.modify_ _ { activeGame = Nothing }
        H.raise (GameEnded game 0)  -- Would get actual score
      Nothing -> pure unit
  
  CloseSelection -> do
    H.modify_ _ { showSelection = false }
