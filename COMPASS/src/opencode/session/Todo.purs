-- | Session Todo - todo list management
module Opencode.Session.Todo where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Effect.Ref (Ref)
import Effect.Ref as Ref

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
  , priority :: String  -- "high", "medium", "low"
  }

-- | Todo storage (in production, would be part of SessionState)
todoStorageRef :: Ref (Map.Map String (Array TodoItem))
todoStorageRef = unsafePerformEffect $ Ref.new Map.empty

-- | Get todos for a session
getTodos :: String -> Aff (Either String (Array TodoItem))
getTodos sessionId = do
  storage <- liftEffect $ Ref.read todoStorageRef
  pure $ Right $ fromMaybe [] (Map.lookup sessionId storage)
  where
    fromMaybe :: forall a. a -> Maybe a -> a
    fromMaybe def = case _ of
      Nothing -> def
      Just x -> x

-- | Add a todo
addTodo :: String -> TodoItem -> Aff (Either String Unit)
addTodo sessionId item = do
  liftEffect $ Ref.modify_ (\storage ->
    let existing = fromMaybe [] (Map.lookup sessionId storage)
        updated = Array.snoc existing item
    in Map.insert sessionId updated storage
  ) todoStorageRef
  pure $ Right unit
  where
    fromMaybe :: forall a. a -> Maybe a -> a
    fromMaybe def = case _ of
      Nothing -> def
      Just x -> x

-- | Update todo status
updateTodo :: String -> String -> TodoStatus -> Aff (Either String Unit)
updateTodo sessionId todoId status = do
  storage <- liftEffect $ Ref.read todoStorageRef
  case Map.lookup sessionId storage of
    Nothing -> pure $ Left "Session not found"
    Just todos -> do
      let updated = Array.map (\todo ->
            if todo.id == todoId
              then todo { status = status }
              else todo
          ) todos
      liftEffect $ Ref.modify_ (\s -> Map.insert sessionId updated s) todoStorageRef
      pure $ Right unit

-- | Write multiple todos (replaces all todos for session)
writeTodos :: String -> Array TodoItem -> Aff (Either String Unit)
writeTodos sessionId items = do
  liftEffect $ Ref.modify_ (\storage -> Map.insert sessionId items storage) todoStorageRef
  pure $ Right unit
