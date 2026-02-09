-- | Debug Scrap command
module Forge.CLI.Cmd.Debug.Scrap where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)

foreign import debugScrapFFI :: Aff (Either String Unit)

-- | Execute debug scrap command
execute :: Aff (Either String Unit)
execute = debugScrapFFI
