-- | ACP Session
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/acp/session.ts
module Opencode.ACP.Session where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | ACP Session info
type ACPSession =
  { id :: String
  , agentId :: String
  , status :: String
  }

-- | Create an ACP session
create :: String -> Aff (Either String ACPSession)
create agentId = notImplemented "ACP.Session.create"

-- | Get ACP session
get :: String -> Aff (Either String ACPSession)
get sessionId = notImplemented "ACP.Session.get"

-- | Close ACP session
close :: String -> Aff (Either String Unit)
close sessionId = notImplemented "ACP.Session.close"
