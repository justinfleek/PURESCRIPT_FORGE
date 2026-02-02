-- | Session Summary - generate session summaries
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/session/summary.ts
module Opencode.Session.Summary where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Session summary
type SessionSummary =
  { sessionId :: String
  , title :: String
  , description :: String
  , messageCount :: Int
  , toolsUsed :: Array String
  , filesModified :: Array String
  , createdAt :: Number
  , updatedAt :: Number
  }

-- | Generate a summary for a session
generateSummary :: String -> Aff (Either String SessionSummary)
generateSummary sessionId = notImplemented "Session.Summary.generateSummary"

-- | Get existing summary
getSummary :: String -> Aff (Either String (Maybe SessionSummary))
getSummary sessionId = notImplemented "Session.Summary.getSummary"
