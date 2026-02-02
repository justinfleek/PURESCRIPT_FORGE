-- | Session Status
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/session/status.ts
module Opencode.Session.Status where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Session status types
data SessionStatus
  = Active
  | Idle
  | Processing
  | WaitingForInput
  | Error String
  | Terminated

-- | Get session status
getStatus :: String -> Aff (Either String SessionStatus)
getStatus sessionId = notImplemented "Session.Status.getStatus"

-- | Set session status
setStatus :: String -> SessionStatus -> Aff (Either String Unit)
setStatus sessionId status = notImplemented "Session.Status.setStatus"
