-- | Session Todo - todo list management
-- | 1:1 from _archive/reference/COMPASS/src/opencode/session/Todo.purs (opencode-original session/todo.ts)
module Forge.Session.Todo where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Data.Array as Array
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Either (Either(..))

-- | Todo item status
data TodoStatus
  = Pending
  | InProgress
  | Completed
  | Cancelled

derive instance eqTodoStatus :: Eq TodoStatus

-- | Todo item
type TodoItem =
  { id :: String
  , content :: String
  , status :: TodoStatus
  , priority :: String
  }

todoStorageRef :: Ref (Map.Map String (Array TodoItem))
todoStorageRef = unsafePerformEffect $ Ref.new Map.empty

getTodos :: String -> Aff (Either String (Array TodoItem))
getTodos sessionId = do
  storage <- liftEffect $ Ref.read todoStorageRef
  pure $ Right $ fromMaybe [] (Map.lookup sessionId storage)

addTodo :: String -> TodoItem -> Aff (Either String Unit)
addTodo sessionId item = do
  liftEffect $ Ref.modify_ (\storage ->
    let existing = fromMaybe [] (Map.lookup sessionId storage)
        updated = Array.snoc existing item
    in Map.insert sessionId updated storage
  ) todoStorageRef
  pure $ Right unit

updateTodo :: String -> String -> TodoStatus -> Aff (Either String Unit)
updateTodo sessionId todoId status = do
  storage <- liftEffect $ Ref.read todoStorageRef
  case Map.lookup sessionId storage of
    Nothing -> pure $ Left "Session not found"
    Just todos -> do
      let updated = Array.map (\todo ->
            if todo.id == todoId then todo { status = status } else todo
          ) todos
      liftEffect $ Ref.modify_ (\s -> Map.insert sessionId updated s) todoStorageRef
      pure $ Right unit

writeTodos :: String -> Array TodoItem -> Aff (Either String Unit)
writeTodos sessionId items = do
  liftEffect $ Ref.modify_ (\storage -> Map.insert sessionId items storage) todoStorageRef
  pure $ Right unit
