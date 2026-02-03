-- | TUI Signal handling
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/tui/util/signal.ts
module Forge.CLI.Cmd.TUI.Util.Signal where

import Prelude
import Effect (Effect)
import Forge.Util.NotImplemented (notImplemented)

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
