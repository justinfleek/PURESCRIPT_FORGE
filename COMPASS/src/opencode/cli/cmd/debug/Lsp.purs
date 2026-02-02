-- | Debug LSP command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/debug/lsp.ts
module Opencode.CLI.Cmd.Debug.Lsp where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Execute debug lsp command
execute :: Aff (Either String Unit)
execute = notImplemented "CLI.Cmd.Debug.Lsp.execute"
