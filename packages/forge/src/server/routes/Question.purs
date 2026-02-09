-- | Question route
-- | 1:1 parity with opencode-dev/packages/opencode/src/server/routes/question.ts
module Forge.Server.Routes.Question where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Foreign (Foreign)

-- | Answer a question
answer :: String -> String -> String -> Aff (Either String Unit)
answer sessionID questionID answerText = answerFFI sessionID questionID answerText

-- | List pending questions
pending :: String -> Aff (Either String (Array Foreign))
pending sessionID = pendingFFI sessionID

foreign import answerFFI :: String -> String -> String -> Aff (Either String Unit)
foreign import pendingFFI :: String -> Aff (Either String (Array Foreign))
