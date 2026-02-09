-- | TUI Signal handling
module Forge.CLI.Cmd.TUI.Util.Signal where

import Prelude
import Effect (Effect)

-- | Signal types
data Signal
  = SIGINT
  | SIGTERM
  | SIGQUIT
  | SIGHUP

-- | Signal handler type
type SignalHandler = Signal -> Effect Unit

-- | FFI imports
foreign import onSignalImpl :: String -> Effect Unit -> Effect Unit
foreign import removeHandlerImpl :: String -> Effect Unit

-- | Convert signal to string name
signalToString :: Signal -> String
signalToString SIGINT = "SIGINT"
signalToString SIGTERM = "SIGTERM"
signalToString SIGQUIT = "SIGQUIT"
signalToString SIGHUP = "SIGHUP"

-- | Register a signal handler
onSignal :: Signal -> SignalHandler -> Effect Unit
onSignal sig handler = onSignalImpl (signalToString sig) (handler sig)

-- | Remove a signal handler
removeHandler :: Signal -> Effect Unit
removeHandler sig = removeHandlerImpl (signalToString sig)
