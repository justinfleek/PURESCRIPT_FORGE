-- | Session command
module Forge.CLI.Cmd.Session where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)

type SessionArgs =
  { list :: Boolean
  , delete :: Maybe String
  , info :: Maybe String
  , export :: Maybe String
  }

-- | Execute the session command
execute :: SessionArgs -> Aff (Either String Unit)
execute args = executeFFI args

foreign import executeFFI :: SessionArgs -> Aff (Either String Unit)
