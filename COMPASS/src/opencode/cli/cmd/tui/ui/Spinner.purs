-- | TUI Spinner component
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/tui/ui/spinner.ts
module Opencode.CLI.Cmd.TUI.UI.Spinner where

import Prelude
import Effect (Effect)
import Opencode.Util.NotImplemented (notImplemented)

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
