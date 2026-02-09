-- | Debug LSP command
module Forge.CLI.Cmd.Debug.Lsp where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)

foreign import debugLspFFI :: Aff (Either String Unit)

-- | Execute debug lsp command
execute :: Aff (Either String Unit)
execute = debugLspFFI
