-- | Run command - main entry point for running opencode
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/run.ts
module Opencode.CLI.Cmd.Run where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

type RunArgs =
  { message :: Array String
  , command :: Maybe String
  , continue :: Boolean
  , session :: Maybe String
  , share :: Boolean
  , model :: Maybe String
  , agent :: Maybe String
  , format :: String  -- "default" or "json"
  , file :: Array String
  , title :: Maybe String
  , attach :: Maybe String
  , port :: Maybe Int
  , variant :: Maybe String
  }

-- | Default run args
defaultArgs :: RunArgs
defaultArgs =
  { message: []
  , command: Nothing
  , continue: false
  , session: Nothing
  , share: false
  , model: Nothing
  , agent: Nothing
  , format: "default"
  , file: []
  , title: Nothing
  , attach: Nothing
  , port: Nothing
  , variant: Nothing
  }

-- | Execute the run command
execute :: RunArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Run.execute"
