{-|
Module      : Tool.Todo
Description : Task list management tool
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

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
module Tool.Todo
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
import Data.Argonaut (Json, class EncodeJson, class DecodeJson, encodeJson, decodeJson)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)

-- ============================================================================
-- TYPES
-- ============================================================================

{-| Single todo item.

@
  record TodoItem where
    id       : String    -- Unique identifier
    content  : String    -- Brief description of the task
    status   : Status    -- Current status
    priority : Priority  -- Priority level
@
-}
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

instance showTodoStatus :: Show TodoStatus where
  show Pending = "pending"
  show InProgress = "in_progress"
  show Completed = "completed"
  show Cancelled = "cancelled"

data Priority
  = High
  | Medium
  | Low

instance showPriority :: Show Priority where
  show High = "high"
  show Medium = "medium"
  show Low = "low"

{-| Parameters for todowrite tool. -}
type TodoWriteParams =
  { todos :: Array TodoItem
  }

{-| Parameters for todoread tool (empty). -}
type TodoReadParams = {}

-- ============================================================================
-- TOOL INTERFACE
-- ============================================================================

{-| Execute todowrite tool.

Updates the todo list with new items.
-}
execute :: TodoWriteParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Validate todo items
  -- 2. Update session todo list
  -- 3. Return confirmation
  let pending = countPending params.todos
  let total = Array.length params.todos
  
  pure
    { title: show pending <> " todos"
    , metadata: encodeJson { todos: params.todos }
    , output: formatTodos params.todos
    , attachments: Nothing
    }

{-| Execute todoread tool.

Reads the current todo list from session.
-}
executeRead :: TodoReadParams -> ToolContext -> Aff ToolResult
executeRead _ ctx = do
  -- TODO: Read from session storage
  let todos = [] :: Array TodoItem
  let pending = countPending todos
  
  pure
    { title: show pending <> " todos"
    , metadata: encodeJson { todos }
    , output: formatTodos todos
    , attachments: Nothing
    }

{-| TodoWrite tool registration. -}
todoWriteTool :: ToolInfo
todoWriteTool =
  { id: "todowrite"
  , description: todoWriteDescription
  , parameters: encodeJson todoWriteSchema
  , execute: \json ctx ->
      case decodeTodoWriteParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Just formatValidationError
  }

{-| TodoRead tool registration. -}
todoReadTool :: ToolInfo
todoReadTool =
  { id: "todoread"
  , description: "Use this tool to read your todo list"
  , parameters: encodeJson emptySchema
  , execute: \json ctx -> executeRead {} ctx
  , formatValidationError: Nothing
  }

-- ============================================================================
-- HELPERS
-- ============================================================================

{-| Count pending (non-completed) todos. -}
countPending :: Array TodoItem -> Int
countPending = Array.length <<< Array.filter (\t -> t.status /= "completed")

{-| Filter todos by status. -}
filterByStatus :: String -> Array TodoItem -> Array TodoItem
filterByStatus status = Array.filter (\t -> t.status == status)

{-| Format todos for output. -}
formatTodos :: Array TodoItem -> String
formatTodos todos = notImplemented "formatTodos"  -- TODO: JSON.stringify equivalent

todoWriteDescription :: String
todoWriteDescription = "Use this tool to create and manage a structured task list for your current coding session."

todoWriteSchema :: { type :: String }
todoWriteSchema = { type: "object" }

emptySchema :: { type :: String }
emptySchema = { type: "object" }

decodeTodoWriteParams :: Json -> Either String TodoWriteParams
decodeTodoWriteParams _ = notImplemented "decodeTodoWriteParams"

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Todo Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationError :: Json -> String
formatValidationError _ = "Invalid todo parameters"

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
