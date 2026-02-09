-- | Debug Agent command
module Forge.CLI.Cmd.Debug.Agent where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)

foreign import debugAgentFFI :: Aff (Either String Unit)

-- | Execute debug agent command
execute :: Aff (Either String Unit)
execute = debugAgentFFI
