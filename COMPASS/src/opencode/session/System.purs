-- | Session System - system message handling
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/session/system.ts
module Opencode.Session.System where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Build the system message for a session
buildSystemMessage :: String -> Aff (Either String String)
buildSystemMessage sessionId = notImplemented "Session.System.buildSystemMessage"

-- | Get base system prompt
getBaseSystemPrompt :: String
getBaseSystemPrompt = "" -- TODO: Implement

-- | Append context to system message
appendContext :: String -> String -> String
appendContext systemMsg context = systemMsg <> "\n\n" <> context
