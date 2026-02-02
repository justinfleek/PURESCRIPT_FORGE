-- | TUI Worker
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/tui/worker.ts
module Opencode.CLI.Cmd.TUI.Worker where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Worker message types
data WorkerMessage
  = Init
  | Process String
  | Shutdown

-- | Start the TUI worker
startWorker :: Aff (Either String Unit)
startWorker = notImplemented "CLI.Cmd.TUI.Worker.startWorker"

-- | Send a message to the worker
sendMessage :: WorkerMessage -> Aff (Either String Unit)
sendMessage msg = notImplemented "CLI.Cmd.TUI.Worker.sendMessage"
