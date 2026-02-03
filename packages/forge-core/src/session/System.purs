-- | Session System - system message handling
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/session/system.ts
module Forge.Session.System where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Build the system message for a session
buildSystemMessage :: String -> Aff (Either String String)
buildSystemMessage sessionId = notImplemented "Session.System.buildSystemMessage"

-- | Get base system prompt
getBaseSystemPrompt :: String
getBaseSystemPrompt = "" -- TODO: Implement

-- | Append context to system message
appendContext :: String -> String -> String
appendContext systemMsg context = systemMsg <> "\n\n" <> context
