{-|
Module      : Forge.Tool.Task
Description : Sub-agent task spawning
= Task Tool

Spawn sub-agents to handle complex, multistep tasks autonomously.

== Coeffect Equation

@
  task : TaskParams -> Graded (Session * Agent agentType) TaskResult

  -- Requires:
  -- 1. Session management (create child session)
  -- 2. Agent access (spawn specified agent type)
@

== Agent Types

| Agent     | Description                              |
|-----------|------------------------------------------|
| general   | General-purpose multi-step tasks         |
| explore   | Codebase exploration and search          |
| research  | Research and analysis                    |

== Usage

@
  task
    { description: "Find auth handlers"
    , prompt: "Search for authentication..."
    , subagentType: "explore"
    , sessionId: Nothing
    }
@

== Session Hierarchy

@
  Parent Session
  |-- Child Session (task)
      |-- Inherits permissions (filtered)
      |-- todowrite: denied
      |-- todoread: denied
      |-- Returns text summary
@
-}
module Forge.Tool.Task
  ( -- * Tool Interface
    TaskParams(..)
  , TaskResult(..)
  , execute
  , taskTool
    -- * Agent Types
  , AgentType(..)
  , availableAgents
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, encodeJson, decodeJson, (.:), (.:?), printJsonDecodeError)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Task tool parameters.
type TaskParams =
  { description :: String
  , prompt :: String
  , subagentType :: String
  , sessionId :: Maybe String
  , command :: Maybe String
  }

type TaskResult =
  { sessionId :: String
  , output :: String
  , toolsCalled :: Array ToolSummary
  }

type ToolSummary =
  { id :: String
  , tool :: String
  , status :: String
  , title :: Maybe String
  }

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
-- AGENT TYPES
-- ============================================================================

-- | Available agent types.
data AgentType
  = General
  | Explore
  | Research

derive instance eqAgentType :: Eq AgentType

instance showAgentType :: Show AgentType where
  show General = "general"
  show Explore = "explore"
  show Research = "research"

agentFromString :: String -> Maybe AgentType
agentFromString = case _ of
  "general" -> Just General
  "explore" -> Just Explore
  "research" -> Just Research
  _ -> Nothing

availableAgents :: Array { name :: String, description :: String }
availableAgents =
  [ { name: "general"
    , description: "General-purpose agent for multi-step tasks"
    }
  , { name: "explore"
    , description: "Fast codebase exploration and search"
    }
  , { name: "research"
    , description: "Research and analysis tasks"
    }
  ]

-- ============================================================================
-- EXECUTION
-- ============================================================================

execute :: TaskParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Validate agent type
  case agentFromString params.subagentType of
    Nothing -> pure $ mkErrorResult 
      ("Unknown agent type: " <> params.subagentType)
    Just agentType -> executeImpl params agentType ctx

executeImpl :: TaskParams -> AgentType -> ToolContext -> Aff ToolResult
executeImpl params agentType ctx = do
  -- Get or create session ID
  sessionId <- case params.sessionId of
    Just sid -> pure sid
    Nothing -> liftEffect generateSessionIdFFI
  
  -- Build system prompt for agent type
  let systemPrompt = agentSystemPrompt agentType
  
  -- Execute sub-agent task via FFI
  result <- executeSubAgentFFI params agentType sessionId systemPrompt
  
  case result of
    Left err -> pure $ mkErrorResult err
    Right output -> pure
      { title: params.description
      , metadata: encodeJson
          { sessionId
          , agentType: show agentType
          , status: "completed"
          }
      , output: output
      , attachments: Nothing
      }

-- | Generate agent-specific system prompt
agentSystemPrompt :: AgentType -> String
agentSystemPrompt = case _ of
  General -> 
    "You are a general-purpose agent. Execute the task step by step, using available tools."
  Explore -> 
    "You are an exploration agent specialized in codebase analysis. Use glob, grep, and read tools efficiently."
  Research ->
    "You are a research agent. Gather information, analyze findings, and provide comprehensive answers."

-- | FFI for session ID generation
foreign import generateSessionIdFFI :: forall a. a

-- | FFI for sub-agent execution
foreign import executeSubAgentFFI :: TaskParams -> AgentType -> String -> String -> Aff (Either String String)

-- ============================================================================
-- TOOL REGISTRATION
-- ============================================================================

taskTool :: ToolInfo
taskTool =
  { id: "task"
  , description: "Spawn sub-agent for complex tasks"
  , parameters: taskSchema
  , execute: \json ctx ->
      case decodeTaskParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Nothing
  }

taskSchema :: Json
taskSchema = encodeJson
  { "type": "object"
  , "properties":
      { "description":
          { "type": "string"
          , "description": "A short (3-5 words) description of the task"
          }
      , "prompt":
          { "type": "string"
          , "description": "The task for the agent to perform"
          }
      , "subagent_type":
          { "type": "string"
          , "description": "The type of specialized agent to use for this task"
          , "enum": ["general", "explore", "research"]
          }
      , "session_id":
          { "type": "string"
          , "description": "Existing Task session to continue"
          }
      , "command":
          { "type": "string"
          , "description": "The command that triggered this task"
          }
      }
  , "required": ["description", "prompt", "subagent_type"]
  }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Task Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

decodeTaskParams :: Json -> Either String TaskParams
decodeTaskParams json =
  case decodeTaskParamsImpl json of
    Left err -> Left (printJsonDecodeError err)
    Right result -> Right result
  where
    decodeTaskParamsImpl j = do
      obj <- decodeJson j
      description <- obj .: "description"
      prompt <- obj .: "prompt"
      subagentType <- obj .: "subagent_type"
      sessionId <- obj .:? "session_id"
      command <- obj .:? "command"
      pure { description, prompt, subagentType, sessionId, command }
