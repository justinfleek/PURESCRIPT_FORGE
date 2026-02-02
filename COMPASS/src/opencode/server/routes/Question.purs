-- | Question route
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/server/routes/question.ts
module Opencode.Server.Routes.Question where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Answer a question
answer :: String -> String -> String -> Aff (Either String Unit)
answer sessionId questionId response = notImplemented "Server.Routes.Question.answer"
