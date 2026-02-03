-- | TUI Worker
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/tui/worker.ts
module Forge.CLI.Cmd.TUI.Worker where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

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
