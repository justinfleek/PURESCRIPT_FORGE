-- | TUI Spinner component
module Forge.CLI.Cmd.TUI.UI.Spinner where

import Prelude
import Effect (Effect)

-- | Spinner configuration
type SpinnerConfig =
  { frames :: Array String
  , interval :: Int
  , text :: String
  }

-- | Default spinner
defaultSpinner :: SpinnerConfig
defaultSpinner =
  { frames: ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"]
  , interval: 80
  , text: "Loading..."
  }

-- | FFI imports
foreign import startImpl :: Array String -> Int -> String -> Effect Unit
foreign import stopImpl :: Effect Unit
foreign import setTextImpl :: String -> Effect Unit

-- | Start a spinner
start :: SpinnerConfig -> Effect Unit
start config = startImpl config.frames config.interval config.text

-- | Stop the spinner
stop :: Effect Unit
stop = stopImpl

-- | Update spinner text
setText :: String -> Effect Unit
setText = setTextImpl
