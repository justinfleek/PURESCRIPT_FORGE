-- | Session Prompt - handle user prompts
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/session/prompt.ts
module Opencode.Session.Prompt where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Prompt request
type PromptRequest =
  { sessionId :: String
  , text :: String
  , files :: Array String
  , model :: Maybe String
  , agent :: Maybe String
  }

-- | Send a prompt to a session
sendPrompt :: PromptRequest -> Aff (Either String Unit)
sendPrompt request = notImplemented "Session.Prompt.sendPrompt"

-- | Execute a command in a session
executeCommand :: String -> String -> String -> Aff (Either String Unit)
executeCommand sessionId command args = notImplemented "Session.Prompt.executeCommand"
