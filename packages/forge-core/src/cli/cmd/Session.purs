-- | Session command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/session.ts
module Forge.CLI.Cmd.Session where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

type SessionArgs =
  { list :: Boolean
  , delete :: Maybe String
  , info :: Maybe String
  , export :: Maybe String
  }

-- | Execute the session command
execute :: SessionArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Session.execute"
