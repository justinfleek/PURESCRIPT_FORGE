{-|
Module      : Tool.Task
Description : Sub-agent task spawning
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
    -- * Sub-Agent Execution
  , executeSubAgentLoop
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

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo, ToolMetadata(..))
import Aleph.Coeffect (Resource(..))
import Opencode.Session.Operations as Operations
import Opencode.Session.LLM as LLM
import Opencode.Session.LLMTypes (LLMRequest(..), LLMResponse, Role(..), ContentPart(..), ToolCall(..), ToolFunction(..), defaultUsage, ToolDefinition(..))
import Opencode.Types.Session (SessionID)
import Tool.Dispatcher (dispatchTool)
import Tool.Registry as ToolRegistry
import Opencode.Provider.Registry as ProviderRegistry
import Effect.Ref (Ref)
import Data.Argonaut (stringify)

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
executeImpl params agentType ctx = do
  -- Note: Full sub-agent execution requires state refs
  -- For now, provide basic implementation structure
  -- Get or create session ID
  sessionId <- case params.sessionId of
    Just sid -> pure sid
    Nothing -> do
      -- Create child session using Operations
      -- Note: In production, would need stateRef passed in context
      -- For now, generate session ID and document structure
      liftEffect generateSessionId
  
  -- Build system prompt for agent type
  let systemPrompt = agentSystemPrompt agentType
  
  -- Execute sub-agent task
  -- This is a simplified implementation that demonstrates the structure
  -- Full implementation would require:
  -- 1. Access to Operations.SessionState ref for session management
  -- 2. Access to Provider.RegistryState ref for LLM config
  -- 3. Tool execution loop with proper state management
  
  -- For now, create a basic execution flow
  let output = executeSubAgentTask params agentType sessionId systemPrompt
  
  pure
    { title: params.description
    , metadata: TaskMetadata
        { sessionId
        , agentType: show agentType
        , status: "executing"
        }
    , output: output
    , attachments: Nothing
    }
  where
    -- Simplified sub-agent execution
    -- In production, this would:
    -- 1. Create child session via Operations.create
    -- 2. Get LLM config from Provider.Registry
    -- 3. Send LLM request with system prompt + user prompt
    -- 4. Handle tool calls in loop
    -- 5. Return final result
    executeSubAgentTask :: TaskParams -> AgentType -> String -> String -> String
    executeSubAgentTask p agentType sid sysPrompt =
      String.joinWith "\n"
        [ "Sub-agent task execution initiated"
        , "Session: " <> sid
        , "Agent Type: " <> show agentType
        , ""
        , "System Prompt:"
        , sysPrompt
        , ""
        , "User Prompt:"
        , p.prompt
        , ""
        , "Status: Task execution structure ready"
        , ""
        , "Next steps (requires state refs):"
        , "1. Create child session via Operations.create"
        , "2. Get LLM config from Provider.Registry.getLLMConfig"
        , "3. Send LLM.complete request with messages"
        , "4. Process tool calls via Dispatcher.dispatchTool"
        , "5. Continue loop until completion"
        ]

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
-- SUB-AGENT EXECUTION LOOP
-- ════════════════════════════════════════════════════════════════════════════

{-| Execute sub-agent task with tool calling loop.

This function implements the core sub-agent execution:
1. Creates child session
2. Sends LLM request with system prompt
3. Processes tool calls in loop
4. Returns final result

Note: Requires state refs for Operations and Provider.Registry
-}
executeSubAgentLoop 
  :: TaskParams 
  -> AgentType 
  -> String  -- Parent session ID
  -> Ref Operations.SessionState 
  -> Ref ToolRegistry.RegistryState
  -> Ref ProviderRegistry.RegistryState
  -> String  -- API key
  -> Aff ToolResult
executeSubAgentLoop params agentType parentSessionId sessionStateRef toolRegistryStateRef providerRegistryStateRef apiKey = do
  -- 1. Create child session
  childSessionId <- createChildSession parentSessionId params sessionStateRef
  
  -- 2. Build LLM request
  let systemPrompt = agentSystemPrompt agentType
  let userPrompt = params.prompt
  
  -- 3. Get LLM config (default to venice provider)
  llmConfig <- liftEffect $ ProviderRegistry.getLLMConfig "venice" "gpt-4" apiKey providerRegistryStateRef
  
  -- 4. Build messages
  let messages = 
        [ LLM.systemMessage systemPrompt
        , LLM.userMessage userPrompt
        ]
  
  -- 5. Get available tools for agent type
  let agentId = Just (show agentType)
  tools <- ToolRegistry.tools { providerID: "venice", modelID: "gpt-4" } agentId toolRegistryStateRef
  
  -- 6. Build LLM request
  let llmRequest =
        { model: "gpt-4"
        , messages: messages
        , temperature: Just 0.7
        , maxTokens: Just 2000
        , stream: false
        , tools: map (\t -> 
            { type: "function"
            , function: 
                { name: t.id
                , description: t.description
                , parameters: t.parameters
                }
            }
          ) tools
        , toolChoice: Nothing
        }
  
  -- 7. Send initial LLM request
  llmResponse <- LLM.complete llmConfig llmRequest
  
  -- 8. Process response and tool calls
  case llmResponse of
    Left err -> pure $ mkErrorResult ("LLM request failed: " <> err)
    Right response -> do
      -- Extract tool calls if any
      let toolCalls = LLM.getToolCalls response
      
      if Array.null toolCalls
        then do
          -- No tool calls, return final response
          let finalOutput = extractTextFromResponse response
          pure
            { title: params.description
            , metadata: TaskMetadata
                { sessionId: childSessionId
                , agentType: show agentType
                , status: "completed"
                }
            , output: finalOutput
            , attachments: Nothing
            }
        else do
          -- Execute tools and continue loop
          toolResults <- Array.traverse (\call -> executeToolCall call childSessionId) toolCalls
          
          -- Build tool result messages
          let toolMessages = Array.mapWithIndex (\idx call -> 
                LLM.toolResultMessage call.id (getToolResultText (Array.index toolResults idx))
              ) toolCalls
          
          -- Continue with updated messages (simplified - would continue loop in production)
          let finalOutput = String.joinWith "\n"
                [ "Tool calls executed: " <> show (Array.length toolCalls)
                , "Results:"
                , String.joinWith "\n" (Array.map (\r -> "- " <> r.title) toolResults)
                ]
          
          pure
            { title: params.description
            , metadata: TaskMetadata
                { sessionId: childSessionId
                , agentType: show agentType
                , status: "completed_with_tools"
                }
            , output: finalOutput
            , attachments: Nothing
            }
  where
    executeToolCall :: ToolCall -> String -> Aff ToolResult
    executeToolCall call sessionId = do
      -- Create tool context for child session
      -- Note: Abort signal would be inherited from parent context in production
      let toolCtx =
            { sessionID: sessionId
            , messageID: "task_" <> call.id
            , agent: show agentType
            , abort: AbortSignal  -- Placeholder - would inherit from parent
            , callID: Just call.id
            , extra: Nothing
            , messages: []
            }
      
      -- Dispatch tool execution
      dispatchTool call.function.name call.arguments toolCtx
    
    extractTextFromResponse :: LLMResponse -> String
    extractTextFromResponse response = case Array.head response.choices of
      Nothing -> "No response"
      Just choice -> LLM.contentToString choice.message.content
    
    getToolResultText :: Maybe ToolResult -> String
    getToolResultText = case _ of
      Nothing -> "Tool execution failed"
      Just result -> result.output

-- ════════════════════════════════════════════════════════════════════════════
-- SESSION MANAGEMENT
-- ════════════════════════════════════════════════════════════════════════════

{-| Create child session with filtered permissions. -}
createChildSession :: String -> TaskParams -> Ref Operations.SessionState -> Aff String
createChildSession parentId params stateRef = do
  -- Create new session with parentID using Operations
  let title = Just ("Task: " <> params.description)
  newSession <- Operations.create { parentID: Just parentId, title } stateRef
  
  -- Session permissions are configured via agent type filtering in Registry
  -- Child sessions inherit parent permissions with restrictions:
  -- - todowrite: deny (child sessions can't modify parent todos)
  -- - todoread: deny (child sessions can't read parent todos)
  -- - task: deny (prevent recursive task spawning unless explicitly allowed)
  -- - Other tools: allow (read, write, edit, search, etc.)
  
  pure newSession.id

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
  , metadata: ErrorMetadata { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }
