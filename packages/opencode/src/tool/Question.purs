-- | Question.purs - User question tool
-- | TODO: Implement - mirrors opencode/src/tool/question.ts
module Tool.Question where

import Prelude
import Data.Maybe (Maybe)
import Effect.Aff (Aff)

type Option = { label :: String, description :: String }
type QuestionDef = { question :: String, header :: String, options :: Array Option, multiple :: Maybe Boolean }
type Params = { questions :: Array QuestionDef }
type Result = { title :: String, output :: String }

execute :: Params -> Aff Result
execute _ = notImplemented "Tool.Question.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
