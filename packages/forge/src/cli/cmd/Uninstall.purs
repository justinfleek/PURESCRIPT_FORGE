-- | Uninstall command
module Forge.CLI.Cmd.Uninstall where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)

type UninstallArgs =
  { force :: Boolean
  , keepData :: Boolean
  }

foreign import uninstallFFI :: Boolean -> Boolean -> Aff (Either String Unit)

-- | Execute the uninstall command
execute :: UninstallArgs -> Aff (Either String Unit)
execute args = uninstallFFI args.force args.keepData
