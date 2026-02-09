-- | Debug File command
module Forge.CLI.Cmd.Debug.File where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)

foreign import debugFileFFI :: String -> Aff (Either String Unit)

-- | Execute debug file command
execute :: String -> Aff (Either String Unit)
execute = debugFileFFI
