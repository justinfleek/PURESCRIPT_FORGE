-- | Todo.purs - Todo list tool
-- | TODO: Implement - mirrors opencode/src/tool/todo.ts
module Tool.Todo where

import Prelude
import Effect.Aff (Aff)

type TodoItem = { id :: String, content :: String, status :: String, priority :: String }
type Params = { todos :: Array TodoItem }
type Result = { title :: String, output :: String }

execute :: Params -> Aff Result
execute _ = notImplemented "Tool.Todo.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
