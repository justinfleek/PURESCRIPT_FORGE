-- | Session Todo - todo list management
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/session/todo.ts
module Forge.Session.Todo where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Todo item status
data TodoStatus
  = Pending
  | InProgress
  | Completed
  | Cancelled

-- | Todo item
type TodoItem =
  { id :: String
  , content :: String
  , status :: TodoStatus
  , priority :: String  -- "high", "medium", "low"
  }

-- | Get todos for a session
getTodos :: String -> Aff (Either String (Array TodoItem))
getTodos sessionId = notImplemented "Session.Todo.getTodos"

-- | Add a todo
addTodo :: String -> TodoItem -> Aff (Either String Unit)
addTodo sessionId item = notImplemented "Session.Todo.addTodo"

-- | Update todo status
updateTodo :: String -> String -> TodoStatus -> Aff (Either String Unit)
updateTodo sessionId todoId status = notImplemented "Session.Todo.updateTodo"

-- | Write multiple todos
writeTodos :: String -> Array TodoItem -> Aff (Either String Unit)
writeTodos sessionId items = notImplemented "Session.Todo.writeTodos"
