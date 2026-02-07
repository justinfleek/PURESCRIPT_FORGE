{-|
Module      : Forge.Tool.Todo
Description : Task list management tool
= Todo Tool

This tool provides task list management for tracking progress during
coding sessions. It helps organize complex tasks and demonstrate
thoroughness to the user.

== Coeffect Equation

@
  todoWrite : TodoParams -> Graded Session Unit
  todoRead  : Unit -> Graded Session (Array TodoItem)

  -- Requires:
  -- 1. Session access for persistent storage
@

== Task States

| State       | Description                        |
|-------------|-----------------------------------|
| pending     | Task not yet started               |
| in_progress | Currently working on               |
| completed   | Task finished successfully         |
| cancelled   | Task no longer needed              |

== Priority Levels

| Priority | Use Case                           |
|----------|-----------------------------------|
| high     | Critical path, blocking tasks      |
| medium   | Important but not blocking         |
| low      | Nice-to-have, can be deferred      |

== Best Practices

1. Only have ONE task in_progress at a time
2. Mark tasks complete immediately after finishing
3. Break complex tasks into smaller steps
4. Use clear, descriptive task names
-}
module Forge.Tool.Todo
  ( -- * Tool Interface
    TodoWriteParams(..)
  , TodoReadParams(..)
  , execute
  , executeRead
  , todoWriteTool
  , todoReadTool
    -- * Todo Types
  , TodoItem(..)
  , TodoStatus(..)
  , Priority(..)
    -- * Helpers
  , countPending
  , filterByStatus
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, encodeJson, decodeJson, (.:), printJsonDecodeError)
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Single todo item.
type TodoItem =
  { id :: String
  , content :: String
  , status :: String      -- "pending" | "in_progress" | "completed" | "cancelled"
  , priority :: String    -- "high" | "medium" | "low"
  }

data TodoStatus
  = Pending
  | InProgress
  | Completed
  | Cancelled

derive instance eqTodoStatus :: Eq TodoStatus

instance showTodoStatus :: Show TodoStatus where
  show Pending = "pending"
  show InProgress = "in_progress"
  show Completed = "completed"
  show Cancelled = "cancelled"

data Priority
  = High
  | Medium
  | Low

derive instance eqPriority :: Eq Priority

instance showPriority :: Show Priority where
  show High = "high"
  show Medium = "medium"
  show Low = "low"

-- | Parameters for todowrite tool.
type TodoWriteParams =
  { todos :: Array TodoItem
  }

-- | Parameters for todoread tool (empty).
type TodoReadParams = {}

-- | Tool result type
type ToolResult =
  { title :: String
  , output :: String
  , metadata :: Json
  , attachments :: Maybe (Array Json)
  }

-- | Tool context
type ToolContext = 
  { workspaceRoot :: String
  , sessionID :: String
  }

-- | Tool info
type ToolInfo =
  { id :: String
  , description :: String
  , parameters :: Json
  , execute :: Json -> ToolContext -> Aff ToolResult
  , formatValidationError :: Maybe (Json -> String)
  }

-- ============================================================================
-- TOOL INTERFACE
-- ============================================================================

-- | Execute todowrite tool.
-- | Updates the todo list with new items.
execute :: TodoWriteParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- Store todos via FFI
  _ <- storeTodosFFI ctx.sessionID params.todos
  
  -- Return confirmation
  let pending = countPending params.todos
  let total = Array.length params.todos
  
  pure
    { title: show pending <> " todos"
    , metadata: encodeJson { todos: params.todos }
    , output: formatTodos params.todos
    , attachments: Nothing
    }

-- | Execute todoread tool.
-- | Reads the current todo list from session.
executeRead :: TodoReadParams -> ToolContext -> Aff ToolResult
executeRead _ ctx = do
  -- Read from session storage via FFI
  todos <- loadTodosFFI ctx.sessionID
  
  let pending = countPending todos
  
  pure
    { title: show pending <> " todos"
    , metadata: encodeJson { todos }
    , output: formatTodos todos
    , attachments: Nothing
    }

-- | FFI for storing todos
foreign import storeTodosFFI :: String -> Array TodoItem -> Aff Unit

-- | FFI for loading todos
foreign import loadTodosFFI :: String -> Aff (Array TodoItem)

-- | TodoWrite tool registration.
todoWriteTool :: ToolInfo
todoWriteTool =
  { id: "todowrite"
  , description: todoWriteDescription
  , parameters: todoWriteSchema
  , execute: \json ctx ->
      case decodeTodoWriteParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Just formatValidationErrorImpl
  }

-- | TodoRead tool registration.
todoReadTool :: ToolInfo
todoReadTool =
  { id: "todoread"
  , description: "Use this tool to read your todo list"
  , parameters: encodeJson { "type": "object" }
  , execute: \json ctx -> executeRead {} ctx
  , formatValidationError: Nothing
  }

-- ============================================================================
-- HELPERS
-- ============================================================================

-- | Count pending (non-completed) todos.
countPending :: Array TodoItem -> Int
countPending = Array.length <<< Array.filter (\t -> t.status /= "completed")

-- | Filter todos by status.
filterByStatus :: String -> Array TodoItem -> Array TodoItem
filterByStatus status = Array.filter (\t -> t.status == status)

-- | Format todos for output.
formatTodos :: Array TodoItem -> String
formatTodos todos =
  if Array.null todos
  then "No todos"
  else String.joinWith "\n" $ Array.mapWithIndex formatTodo todos
  where
    formatTodo idx todo =
      let statusIcon = case todo.status of
            "completed" -> "[x]"
            "in_progress" -> "[>]"
            "cancelled" -> "[-]"
            _ -> "[ ]"
          priorityPrefix = case todo.priority of
            "high" -> "[HIGH]"
            "medium" -> "[MED]"
            "low" -> "[LOW]"
            _ -> ""
      in show (idx + 1) <> ". " <> statusIcon <> " " <> priorityPrefix <> " " <> todo.content <> " (" <> todo.status <> ")"

todoWriteDescription :: String
todoWriteDescription = "Use this tool to create and manage a structured task list for your current coding session."

todoWriteSchema :: Json
todoWriteSchema = encodeJson
  { "type": "object"
  , "properties":
      { "todos":
          { "type": "array"
          , "items":
              { "type": "object"
              , "properties":
                  { "id": { "type": "string", "description": "Unique identifier for the todo item" }
                  , "content": { "type": "string", "description": "Brief description of the task" }
                  , "status": { "type": "string", "enum": ["pending", "in_progress", "completed", "cancelled"], "description": "Current status of the task" }
                  , "priority": { "type": "string", "enum": ["high", "medium", "low"], "description": "Priority level of the task" }
                  }
              , "required": ["id", "content", "status", "priority"]
              }
          , "description": "The updated todo list"
          }
      }
  , "required": ["todos"]
  }

decodeTodoWriteParams :: Json -> Either String TodoWriteParams
decodeTodoWriteParams json =
  case decodeTodoWriteParamsImpl json of
    Left err -> Left (printJsonDecodeError err)
    Right result -> Right result
  where
    decodeTodoWriteParamsImpl j = do
      obj <- decodeJson j
      todos <- obj .: "todos"
      pure { todos }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Todo Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationErrorImpl :: Json -> String
formatValidationErrorImpl _ = "Invalid todo parameters"
