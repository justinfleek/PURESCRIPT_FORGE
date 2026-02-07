{-|
Module      : Sidepanel.Components.EasterEggs.Doom.DoomTypes
Description : Types for Doom game integration
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

Types for Doom game integration via js-dos.
-}
module Sidepanel.Components.EasterEggs.Doom.DoomTypes where

import Prelude

-- | Doom game state
type DoomState =
  { isLoaded :: Boolean
  , isRunning :: Boolean
  , isPaused :: Boolean
  , wadFile :: Maybe String
  , saveState :: Maybe String
  , volume :: Number  -- 0.0 to 1.0
  }

-- | Doom action
data DoomAction
  = LoadWAD String
  | Start
  | Pause
  | Resume
  | Stop
  | SaveState
  | LoadState String
  | SetVolume Number
  | FullScreen Boolean

derive instance eqDoomAction :: Eq DoomAction

-- | Initial Doom state
initialDoomState :: DoomState
initialDoomState =
  { isLoaded: false
  , isRunning: false
  , isPaused: false
  , wadFile: Nothing
  , saveState: Nothing
  , volume: 0.7
  }

-- | Doom control keys
type DoomControls =
  { moveForward :: String
  , moveBackward :: String
  , turnLeft :: String
  , turnRight :: String
  , strafeLeft :: String
  , strafeRight :: String
  , fire :: String
  , use :: String
  , run :: String
  }

-- | Default controls (WASD + arrows)
defaultControls :: DoomControls
defaultControls =
  { moveForward: "w"
  , moveBackward: "s"
  , turnLeft: "a"
  , turnRight: "d"
  , strafeLeft: "q"
  , strafeRight: "e"
  , fire: " "
  , use: "f"
  , run: "Shift"
  }
