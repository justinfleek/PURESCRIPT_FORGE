-- | Session route
-- | 1:1 parity with opencode-dev/packages/opencode/src/server/routes/session.ts
module Forge.Server.Routes.Session where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Foreign (Foreign)

import Forge.Session.Session as Session

-- | Create a new session
create :: Maybe { parentID :: Maybe String, title :: Maybe String } -> Aff (Either String Foreign)
create input = createFFI input

-- | List all sessions
list :: Aff (Either String (Array Foreign))
list = listFFI

-- | Get session by ID
get :: String -> Aff (Either String (Maybe Foreign))
get sessionID = getFFI sessionID

-- | Get session messages
messages :: String -> Maybe Int -> Aff (Either String (Array Foreign))
messages sessionID limit = messagesFFI sessionID limit

-- | Send prompt to session
prompt :: String -> String -> Aff (Either String Foreign)
prompt sessionID text = promptFFI sessionID text

-- | Execute command in session
command :: String -> String -> String -> Aff (Either String Foreign)
command sessionID cmd args = commandFFI sessionID cmd args

-- | Share session
share :: String -> Aff (Either String Foreign)
share sessionID = shareFFI sessionID

-- | Unshare session
unshare :: String -> Aff (Either String Unit)
unshare sessionID = unshareFFI sessionID

-- | Delete session
delete :: String -> Aff (Either String Unit)
delete sessionID = deleteFFI sessionID

-- | Fork session
fork :: String -> Maybe String -> Aff (Either String Foreign)
fork sessionID messageID = forkFFI sessionID messageID

-- | Abort session processing
abort :: String -> Aff (Either String Unit)
abort sessionID = abortFFI sessionID

-- | FFI imports
foreign import createFFI :: Maybe { parentID :: Maybe String, title :: Maybe String } -> Aff (Either String Foreign)
foreign import listFFI :: Aff (Either String (Array Foreign))
foreign import getFFI :: String -> Aff (Either String (Maybe Foreign))
foreign import messagesFFI :: String -> Maybe Int -> Aff (Either String (Array Foreign))
foreign import promptFFI :: String -> String -> Aff (Either String Foreign)
foreign import commandFFI :: String -> String -> String -> Aff (Either String Foreign)
foreign import shareFFI :: String -> Aff (Either String Foreign)
foreign import unshareFFI :: String -> Aff (Either String Unit)
foreign import deleteFFI :: String -> Aff (Either String Unit)
foreign import forkFFI :: String -> Maybe String -> Aff (Either String Foreign)
foreign import abortFFI :: String -> Aff (Either String Unit)
