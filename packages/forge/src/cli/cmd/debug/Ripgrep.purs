-- | Debug Ripgrep command
module Forge.CLI.Cmd.Debug.Ripgrep where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)

foreign import debugRipgrepFFI :: String -> Aff (Either String Unit)

-- | Execute debug ripgrep command
execute :: String -> Aff (Either String Unit)
execute = debugRipgrepFFI
