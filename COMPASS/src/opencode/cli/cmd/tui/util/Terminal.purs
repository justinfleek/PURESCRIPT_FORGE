-- | TUI Terminal utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/tui/util/terminal.ts
module Opencode.CLI.Cmd.TUI.Util.Terminal where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Terminal size
type TerminalSize =
  { width :: Int
  , height :: Int
  }

-- | Get terminal size
getSize :: Effect (Maybe TerminalSize)
getSize = notImplemented "CLI.Cmd.TUI.Util.Terminal.getSize"

-- | Check if running in a TTY
isTTY :: Effect Boolean
isTTY = notImplemented "CLI.Cmd.TUI.Util.Terminal.isTTY"

-- | Enable raw mode
enableRawMode :: Effect Unit
enableRawMode = notImplemented "CLI.Cmd.TUI.Util.Terminal.enableRawMode"

-- | Disable raw mode
disableRawMode :: Effect Unit
disableRawMode = notImplemented "CLI.Cmd.TUI.Util.Terminal.disableRawMode"

-- | Clear the terminal
clear :: Effect Unit
clear = notImplemented "CLI.Cmd.TUI.Util.Terminal.clear"

-- | Move cursor
moveCursor :: Int -> Int -> Effect Unit
moveCursor x y = notImplemented "CLI.Cmd.TUI.Util.Terminal.moveCursor"
