-- | TUI Spinner component
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/tui/ui/spinner.ts
module Forge.CLI.Cmd.TUI.UI.Spinner where

import Prelude
import Effect (Effect)
import Forge.Util.NotImplemented (notImplemented)

-- | Spinner configuration
type SpinnerConfig =
  { frames :: Array String
  , interval :: Int  -- milliseconds
  , text :: String
  }

-- | Default spinner
defaultSpinner :: SpinnerConfig
defaultSpinner =
  { frames: ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"]
  , interval: 80
  , text: "Loading..."
  }

-- | Start a spinner
start :: SpinnerConfig -> Effect Unit
start config = notImplemented "CLI.Cmd.TUI.UI.Spinner.start"

-- | Stop the spinner
stop :: Effect Unit
stop = notImplemented "CLI.Cmd.TUI.UI.Spinner.stop"

-- | Update spinner text
setText :: String -> Effect Unit
setText text = notImplemented "CLI.Cmd.TUI.UI.Spinner.setText"
