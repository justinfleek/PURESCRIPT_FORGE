-- | Question handling
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/question/index.ts
module Forge.Question.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Question type
type Question =
  { id :: String
  , sessionId :: String
  , question :: String
  , options :: Array QuestionOption
  , multiple :: Boolean
  }

-- | Question option
type QuestionOption =
  { label :: String
  , description :: Maybe String
  }

-- | Ask a question
ask :: String -> Question -> Aff (Either String Unit)
ask sessionId question = notImplemented "Question.Index.ask"

-- | Answer a question
answer :: String -> String -> Array String -> Aff (Either String Unit)
answer sessionId questionId answers = notImplemented "Question.Index.answer"
