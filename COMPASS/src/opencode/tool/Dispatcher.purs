{-|
Module      : Tool.Dispatcher
Description : Global tool dispatcher for executing tools by ID
|= Tool Dispatcher

Central dispatcher that maps tool IDs to their execute functions.
Imports all tools and provides lookup functionality.

== Coeffect Equation

@
  dispatch : ToolID × Json × Context -> Graded (ToolRegistry) ToolResult
@
-}
module Tool.Dispatcher
  ( -- * Tool Execution
    dispatchTool
  , getToolExecute
    -- * Tool Registry
  , toolRegistry
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Argonaut (Json)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)

-- Import all tool definitions
import Tool.Search as Search
import Tool.Bash as Bash
import Tool.Todo as Todo
import Tool.Batch as Batch
import Tool.Multiedit as Multiedit
import Tool.Question as Question
import Tool.Ls as Ls
import Tool.Skill as Skill
import Tool.Lsp as Lsp
import Tool.Codesearch as Codesearch
import Tool.Websearch as Websearch
import Tool.Task as Task
import Tool.Plan as Plan

-- ============================================================================
-- TOOL REGISTRY
-- ============================================================================

-- | Global tool registry mapping IDs to ToolInfo
toolRegistry :: Map String ToolInfo
toolRegistry = Map.fromFoldable
  [ { key: "search", value: Search.searchTool }
  , { key: "bash", value: Bash.bashTool }
  , { key: "todowrite", value: Todo.todoWriteTool }
  , { key: "todoread", value: Todo.todoReadTool }
  , { key: "batch", value: Batch.batchTool }
  , { key: "multiedit", value: Multiedit.multieditTool }
  , { key: "question", value: Question.questionTool }
  , { key: "list", value: Ls.lsTool }
  , { key: "skill", value: Skill.skillTool }
  , { key: "lsp", value: Lsp.lspTool }
  , { key: "codesearch", value: Codesearch.codesearchTool }
  , { key: "websearch", value: Websearch.websearchTool }
  , { key: "task", value: Task.taskTool }
  , { key: "plan_exit", value: Plan.planExitTool }
  , { key: "plan_enter", value: Plan.planEnterTool }
  ]

-- ============================================================================
-- TOOL EXECUTION
-- ============================================================================

{-| Get execute function for a tool by ID. -}
getToolExecute :: String -> Maybe (Json -> ToolContext -> Aff ToolResult)
getToolExecute toolId = do
  toolInfo <- Map.lookup toolId toolRegistry
  pure toolInfo.execute

{-| Dispatch a tool call to the appropriate tool executor.
Looks up the tool's execute function and calls it with the parameters.
-}
dispatchTool :: String -> Json -> ToolContext -> Aff ToolResult
dispatchTool toolId parameters ctx = do
  case getToolExecute toolId of
    Nothing -> pure
      { title: "Tool Error: " <> toolId
      , metadata: ErrorMetadata { error: "Tool not found: " <> toolId }
      , output: "Error: Tool '" <> toolId <> "' is not registered in the tool registry."
      , attachments: Nothing
      }
    Just executeFn -> executeFn parameters ctx
