{-|
Module      : Sidepanel.Components.EasterEggs.Doom.Doom
Description : Main Doom game component (js-dos integration)
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

Main Halogen component for Doom game via js-dos emulator.
-}
module Sidepanel.Components.EasterEggs.Doom.Doom where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Class (liftEffect)
import Effect.Aff.Class (class MonadAff)
import Effect.Aff (Aff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Sidepanel.Components.EasterEggs.Doom.DoomTypes
  ( DoomState
  , DoomAction(..)
  , initialDoomState
  , defaultControls
  )

-- | Component state
type State =
  { doomState :: DoomState
  , controls :: DoomControls
  , isInitialized :: Boolean
  }

-- | Component actions
data Action
  = Initialize
  | HandleKeyPress String Boolean
  | LoadWAD String
  | Start
  | Pause
  | Resume
  | Stop
  | SaveState
  | LoadState
  | SetVolume Number
  | FullScreen Boolean

-- | Component output
data Output
  = DoomLoaded
  | DoomStarted
  | DoomStopped
  | StateSaved
  | StateLoaded

-- | Import DoomControls
import Sidepanel.Components.EasterEggs.Doom.DoomTypes (DoomControls)

-- | Component input
type Input = Unit

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \_ ->
      { doomState: initialDoomState
      , controls: defaultControls
      , isInitialized: false
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
    [ HP.class_ (H.ClassName "doom-game") ]
    [ HH.canvas
        [ HP.id "doom-canvas"
        , HP.width 640
        , HP.height 400
        , HP.class_ (H.ClassName "doom-canvas")
        ]
    , HH.div
        [ HP.class_ (H.ClassName "doom-controls") ]
        [ HH.button
            [ HP.class_ (H.ClassName "doom-btn")
            , HE.onClick \_ -> Start
            , HP.disabled (not state.doomState.isLoaded || state.doomState.isRunning)
            ]
            [ HH.text "Start" ]
        , HH.button
            [ HP.class_ (H.ClassName "doom-btn")
            , HE.onClick \_ -> if state.doomState.isPaused then Resume else Pause
            , HP.disabled (not state.doomState.isRunning)
            ]
            [ HH.text (if state.doomState.isPaused then "Resume" else "Pause") ]
        , HH.button
            [ HP.class_ (H.ClassName "doom-btn")
            , HE.onClick \_ -> Stop
            , HP.disabled (not state.doomState.isRunning)
            ]
            [ HH.text "Stop" ]
        , HH.button
            [ HP.class_ (H.ClassName "doom-btn")
            , HE.onClick \_ -> SaveState
            , HP.disabled (not state.doomState.isRunning)
            ]
            [ HH.text "Quick Save (F6)" ]
        , HH.button
            [ HP.class_ (H.ClassName "doom-btn")
            , HE.onClick \_ -> LoadState
            , HP.disabled (not state.doomState.isRunning)
            ]
            [ HH.text "Quick Load (F9)" ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "doom-instructions") ]
        [ HH.p_ [ HH.text "WASD: Move" ]
        , HH.p_ [ HH.text "Arrow Keys: Turn" ]
        , HH.p_ [ HH.text "Space: Fire" ]
        , HH.p_ [ HH.text "F: Use/Open" ]
        , HH.p_ [ HH.text "Shift: Run" ]
        , HH.p_ [ HH.text "F6: Quick Save, F9: Quick Load" ]
        ]
    , if not state.isInitialized then
        HH.div
          [ HP.class_ (H.ClassName "doom-loading") ]
          [ HH.p_ [ HH.text "Loading Doom emulator..." ] ]
      else
        HH.text ""
    ]

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Initialize js-dos
    initResult <- initDosbox
    case initResult of
      Left err -> pure unit  -- Would show error
      Right _ -> do
        -- Create emulator
        createResult <- createEmulator "doom-canvas"
        case createResult of
          Left err -> pure unit
          Right _ -> do
            H.modify_ _ { isInitialized = true }
            -- Auto-load Doom shareware
            handleAction (LoadWAD "https://js-dos.com/games/doom.zip")
  
  LoadWAD wadUrl -> do
    state <- H.get
    loadResult <- loadDoom wadUrl
    case loadResult of
      Left err -> pure unit  -- Would show error
      Right _ -> do
        H.modify_ \s -> s
          { doomState = s.doomState
              { isLoaded = true
              , wadFile = Just wadUrl
              }
          }
        H.raise DoomLoaded
  
  Start -> do
    state <- H.get
    if state.doomState.isLoaded && not state.doomState.isRunning then
      do
        H.modify_ \s -> s
          { doomState = s.doomState { isRunning = true, isPaused = false } }
        H.raise DoomStarted
    else
      pure unit
  
  Pause -> do
    state <- H.get
    liftEffect pauseEmulator
    H.modify_ \s -> s { doomState = s.doomState { isPaused = true } }
  
  Resume -> do
    state <- H.get
    liftEffect resumeEmulator
    H.modify_ \s -> s { doomState = s.doomState { isPaused = false } }
  
  Stop -> do
    state <- H.get
    liftEffect stopEmulator
    H.modify_ \s -> s
      { doomState = s.doomState
          { isRunning = false
          , isPaused = false
          }
      }
    H.raise DoomStopped
  
  HandleKeyPress key pressed -> do
    state <- H.get
    if state.doomState.isRunning && not state.doomState.isPaused then
      liftEffect $ sendKey key pressed
    else
      pure unit
  
  SaveState -> do
    state <- H.get
    if state.doomState.isRunning then
      do
        saveResult <- saveState
        case saveResult of
          Left err -> pure unit
          Right _ -> do
            H.raise StateSaved
    else
      pure unit
  
  LoadState -> do
    state <- H.get
    if state.doomState.isRunning then
      do
        loadResult <- loadState
        case loadResult of
          Left err -> pure unit
          Right _ -> do
            H.raise StateLoaded
    else
      pure unit
  
  SetVolume volume -> do
    liftEffect $ setVolume volume
    H.modify_ \s -> s { doomState = s.doomState { volume = volume } }
  
  FullScreen fullscreen -> do
    -- Would toggle fullscreen mode
    pure unit

-- | FFI imports
foreign import initDosbox :: Aff (Either String Unit)
foreign import createEmulator :: String -> Aff (Either String Unit)
foreign import loadDoom :: String -> Aff (Either String Unit)
foreign import sendKey :: String -> Boolean -> Effect Unit
foreign import pauseEmulator :: Effect Unit
foreign import resumeEmulator :: Effect Unit
foreign import stopEmulator :: Effect Unit
foreign import saveState :: Aff (Either String String)
foreign import loadState :: Aff (Either String String)
foreign import setVolume :: Number -> Effect Unit
