-- | Auth command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/auth.ts
module Opencode.CLI.Cmd.Auth where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

type AuthArgs =
  { login :: Boolean
  , logout :: Boolean
  , status :: Boolean
  , provider :: Maybe String
  }

-- | Execute the auth command
execute :: AuthArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Auth.execute"

-- | Login to a provider
login :: String -> Aff (Either String Unit)
login provider = notImplemented "CLI.Cmd.Auth.login"

-- | Logout from current session
logout :: Aff (Either String Unit)
logout = notImplemented "CLI.Cmd.Auth.logout"

-- | Check auth status
status :: Aff (Either String String)
status = notImplemented "CLI.Cmd.Auth.status"
