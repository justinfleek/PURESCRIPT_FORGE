-- | Session Revert - revert to previous state
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/session/revert.ts
module Opencode.Session.Revert where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Revert result
type RevertResult =
  { messagesRemoved :: Int
  , revertedToId :: String
  }

-- | Revert to a specific message
revertToMessage :: String -> String -> Aff (Either String RevertResult)
revertToMessage sessionId messageId = notImplemented "Session.Revert.revertToMessage"

-- | Revert last N messages
revertLast :: String -> Int -> Aff (Either String RevertResult)
revertLast sessionId count = notImplemented "Session.Revert.revertLast"

-- | Undo last action
undo :: String -> Aff (Either String RevertResult)
undo sessionId = notImplemented "Session.Revert.undo"
