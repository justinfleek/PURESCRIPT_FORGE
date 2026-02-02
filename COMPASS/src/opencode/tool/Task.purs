{-|
Module      : Tool.Task
Description : Sub-agent task spawning
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Task Tool

Spawn sub-agents to handle complex, multistep tasks autonomously.

== Coeffect Equation

@
  task : TaskParams → Graded (Session ⊗ Agent agentType) TaskResult

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
  └── Child Session (task)
      ├── Inherits permissions (filtered)
      ├── todowrite: denied
      ├── todoread: denied
      └── Returns text summary
@
-}
module Tool.Task
  ( -- * Tool Interface
    TaskParams(..)
  , TaskResult(..)
  , execute
  , taskTool
    -- * Agent Types
  , AgentType(..)
  , availableAgents
    -- * Session Management
  , createChildSession
    -- * Coeffects
  , taskCoeffect
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Argonaut (Json, encodeJson, decodeJson)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Aleph.Coeffect (Resource(..))

-- ════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ════════════════════════════════════════════════════════════════════════════

{-| Task tool parameters.

@
  record TaskParams where
    description  : String        -- Short task description
    prompt       : String        -- Full task prompt
    subagentType : String        -- Agent type to spawn
    sessionId    : Maybe String  -- Continue existing session
    command      : Maybe String  -- Triggering command
@
-}
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

-- ════════════════════════════════════════════════════════════════════════════
-- AGENT TYPES
-- ════════════════════════════════════════════════════════════════════════════

{-| Available agent types.

@
  data AgentType where
    General  : AgentType  -- Multi-step tasks
    Explore  : AgentType  -- Codebase exploration
    Research : AgentType  -- Research and analysis
@
-}
data AgentType
  = General
  | Explore
  | Research

derive instance eqAgentType :: Eq AgentType
derive instance genericAgentType :: Generic AgentType _

instance showAgentType :: Show AgentType where
  show = genericShow

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

-- ════════════════════════════════════════════════════════════════════════════
-- EXECUTION
-- ════════════════════════════════════════════════════════════════════════════

execute :: TaskParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Validate agent type
  case agentFromString params.subagentType of
    Nothing -> pure $ mkErrorResult 
      ("Unknown agent type: " <> params.subagentType)
    Just agentType -> executeImpl params agentType ctx

executeImpl :: TaskParams -> AgentType -> ToolContext -> Aff ToolResult
executeImpl params agentType _ctx = do
  -- Get or create session ID
  sessionId <- case params.sessionId of
    Just sid -> pure sid
    Nothing -> liftEffect generateSessionId
  
  -- Build system prompt for agent type
  let _systemPrompt = agentSystemPrompt agentType
  
  -- NOTE: Full sub-agent implementation requires:
  -- 1. Venice client to send chat request
  -- 2. Session store to track child session
  -- 3. Tool execution loop for sub-agent
  -- For now, return a stub indicating the infrastructure needed
  
  pure
    { title: params.description
    , metadata: encodeJson
        { sessionId
        , agentType: show agentType
        , status: "pending_implementation"
        }
    , output: formatTaskOutput params agentType sessionId
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

-- | Format task output
formatTaskOutput :: TaskParams -> AgentType -> String -> String
formatTaskOutput params agentType sessionId =
  String.joinWith "\n"
    [ "Task: " <> params.description
    , "Agent: " <> show agentType
    , "Session: " <> sessionId
    , ""
    , "Prompt:"
    , params.prompt
    , ""
    , "Status: Awaiting full agent infrastructure"
    , ""
    , "Required for completion:"
    , "- Venice chat integration for LLM calls"
    , "- Session management for child sessions"  
    , "- Tool execution loop for sub-agent"
    ]

-- | Generate session ID
foreign import generateSessionId :: Effect String

-- ════════════════════════════════════════════════════════════════════════════
-- SESSION MANAGEMENT
-- ════════════════════════════════════════════════════════════════════════════

{-| Create child session with filtered permissions. -}
createChildSession :: String -> TaskParams -> Aff String
createChildSession parentId params = do
  -- TODO: Implement session creation
  -- 1. Create new session with parentID
  -- 2. Configure permissions:
  --    - todowrite: deny
  --    - todoread: deny
  --    - task: deny (unless agent has permission)
  pure ""

-- ════════════════════════════════════════════════════════════════════════════
-- COEFFECTS
-- ════════════════════════════════════════════════════════════════════════════

{-| Coeffect for task operations.

Task requires session and agent access.
-}
taskCoeffect :: TaskParams -> Resource
taskCoeffect params = Auth ("agent:" <> params.subagentType)

-- ════════════════════════════════════════════════════════════════════════════
-- TOOL REGISTRATION
-- ════════════════════════════════════════════════════════════════════════════

taskTool :: ToolInfo
taskTool =
  { id: "task"
  , description: "Spawn sub-agent for complex tasks"
  , parameters: taskSchema
  , execute: \json ctx ->
      case decodeJson json of
        Left err -> pure $ mkErrorResult (show err)
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
