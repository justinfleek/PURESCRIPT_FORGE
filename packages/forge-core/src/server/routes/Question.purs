-- | Question route
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/server/routes/question.ts
module Forge.Server.Routes.Question where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Answer a question
answer :: String -> String -> String -> Aff (Either String Unit)
answer sessionId questionId response = notImplemented "Server.Routes.Question.answer"
