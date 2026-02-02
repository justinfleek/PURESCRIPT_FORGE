-- | TUI Signal handling
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/tui/util/signal.ts
module Opencode.CLI.Cmd.TUI.Util.Signal where

import Prelude
import Effect (Effect)
import Opencode.Util.NotImplemented (notImplemented)

-- | Signal types
data Signal
  = SIGINT
  | SIGTERM
  | SIGQUIT
  | SIGHUP

-- | Signal handler type
type SignalHandler = Signal -> Effect Unit

-- | Register a signal handler
onSignal :: Signal -> SignalHandler -> Effect Unit
onSignal signal handler = notImplemented "CLI.Cmd.TUI.Util.Signal.onSignal"

-- | Remove a signal handler
removeHandler :: Signal -> Effect Unit
removeHandler signal = notImplemented "CLI.Cmd.TUI.Util.Signal.removeHandler"
