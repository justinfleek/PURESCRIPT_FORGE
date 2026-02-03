-- | Debug LSP command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/debug/lsp.ts
module Forge.CLI.Cmd.Debug.Lsp where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Execute debug lsp command
execute :: Aff (Either String Unit)
execute = notImplemented "CLI.Cmd.Debug.Lsp.execute"
