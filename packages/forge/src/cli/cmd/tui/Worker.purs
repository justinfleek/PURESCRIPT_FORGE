-- | TUI Worker
-- | Ported from: opencode-dev/packages/forge/src/cli/cmd/tui/worker.ts
module Forge.CLI.Cmd.TUI.Worker where

import Prelude

import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Worker message types
data WorkerMessage
  = Init
  | Process String
  | Shutdown

-- | Start the TUI worker
startWorker :: Aff (Either String Unit)
startWorker = fromEffectFnAff startWorkerFFI

-- | Send a message to the worker
sendMessage :: WorkerMessage -> Aff (Either String Unit)
sendMessage msg = fromEffectFnAff (sendWorkerMessageFFI (encodeMessage msg))
  where
    encodeMessage :: WorkerMessage -> String
    encodeMessage Init = "init"
    encodeMessage (Process s) = "process:" <> s
    encodeMessage Shutdown = "shutdown"

-- | Stop the worker
stopWorker :: Aff (Either String Unit)
stopWorker = sendMessage Shutdown

-- | FFI: Start worker
foreign import startWorkerFFI :: EffectFnAff (Either String Unit)

-- | FFI: Send message to worker
foreign import sendWorkerMessageFFI :: String -> EffectFnAff (Either String Unit)
