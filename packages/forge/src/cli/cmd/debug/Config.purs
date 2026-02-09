-- | Debug Config command
module Forge.CLI.Cmd.Debug.Config where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)

foreign import readConfigFFI :: Aff (Either String Unit)

-- | Execute debug config command
execute :: Aff (Either String Unit)
execute = readConfigFFI
