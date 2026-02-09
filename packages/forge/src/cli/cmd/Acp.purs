-- | ACP (Agent Collaboration Protocol) command
module Forge.CLI.Cmd.Acp where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)

type AcpArgs =
  { action :: String
  , target :: String
  }

foreign import acpExecuteFFI :: String -> String -> Aff (Either String Unit)

-- | Execute the ACP command
execute :: AcpArgs -> Aff (Either String Unit)
execute args = acpExecuteFFI args.action args.target
