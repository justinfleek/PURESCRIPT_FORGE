-- | Session route
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/server/routes/session.ts
module Forge.Server.Routes.Session where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Create a new session
create :: Maybe String -> Aff (Either String String)
create title = notImplemented "Server.Routes.Session.create"

-- | List sessions
list :: Aff (Either String (Array String))
list = notImplemented "Server.Routes.Session.list"

-- | Get session
get :: String -> Aff (Either String String)
get sessionId = notImplemented "Server.Routes.Session.get"

-- | Send prompt to session
prompt :: String -> String -> Aff (Either String Unit)
prompt sessionId message = notImplemented "Server.Routes.Session.prompt"

-- | Run command in session
command :: String -> String -> String -> Aff (Either String Unit)
command sessionId cmd args = notImplemented "Server.Routes.Session.command"

-- | Share session
share :: String -> Aff (Either String String)
share sessionId = notImplemented "Server.Routes.Session.share"
