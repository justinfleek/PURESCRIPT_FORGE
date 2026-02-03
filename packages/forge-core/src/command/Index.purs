-- | Command system
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/command/index.ts
module Forge.Command.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Command definition
type Command =
  { name :: String
  , description :: String
  , pattern :: String
  }

-- | Get a command by name
get :: String -> Aff (Maybe Command)
get name = notImplemented "Command.Index.get"

-- | List all commands
list :: Aff (Either String (Array Command))
list = notImplemented "Command.Index.list"

-- | Execute a command
execute :: String -> String -> Aff (Either String String)
execute name args = notImplemented "Command.Index.execute"
