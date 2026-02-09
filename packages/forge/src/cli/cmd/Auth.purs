-- | Auth command
module Forge.CLI.Cmd.Auth where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)

type AuthArgs =
  { login :: Boolean
  , logout :: Boolean
  , status :: Boolean
  , provider :: Maybe String
  }

-- | Execute the auth command
execute :: AuthArgs -> Aff (Either String Unit)
execute args = executeFFI args

-- | Login to a provider
login :: String -> Aff (Either String Unit)
login provider = loginFFI provider

-- | Logout from current session
logout :: Aff (Either String Unit)
logout = logoutFFI

-- | Check auth status
status :: Aff (Either String String)
status = statusFFI

foreign import executeFFI :: AuthArgs -> Aff (Either String Unit)
foreign import loginFFI :: String -> Aff (Either String Unit)
foreign import logoutFFI :: Aff (Either String Unit)
foreign import statusFFI :: Aff (Either String String)
