-- | Session Summary
-- |
-- | Generates summaries and diffs for sessions and messages.
-- |
-- | 1:1 parity with opencode-dev/packages/opencode/src/session/summary.ts
module Forge.Session.Summary
  ( summarize
  , diff
  , computeDiff
  ) where

import Prelude
import Effect.Aff (Aff)
import Foreign (Foreign)
import Data.Maybe (Maybe)

-- | Summarize a session and message
foreign import summarize :: 
  { sessionID :: String
  , messageID :: String
  } -> Aff Unit

-- | Get diff for session
foreign import diff :: 
  { sessionID :: String
  , messageID :: Maybe String
  } -> Aff (Array Foreign)

-- | Compute diff from messages
foreign import computeDiff :: 
  { messages :: Array Foreign
  } -> Aff (Array Foreign)
