{-|
Module      : Forge.Agent.Agent
Description : Agent System

The agent system defines different agent personalities and capabilities.
Agents determine how the AI assistant behaves, what tools it has access to,
and what system prompts guide its responses.

== Built-in Agents

| Agent    | Description                          | Mode     |
|----------|--------------------------------------|----------|
| default  | General-purpose assistant            | Primary  |
| coder    | Code-focused assistant               | Primary  |
| explore  | Fast exploration agent               | Subagent |
| research | Research and analysis agent          | Subagent |
| plan     | Planning mode (read-only)            | Primary  |

== Custom Agents

Custom agents can be defined in `.forge/agents.json`:
@
{
  "agents": [
    {
      "id": "my-agent",
      "name": "My Custom Agent",
      "description": "A custom agent",
      "systemPrompt": "You are a helpful assistant..."
    }
  ]
}
@
-}
module Forge.Agent.Agent
  ( -- * Types
    Agent
  , AgentMode(..)
  , AgentConfig
    -- * Agent Lookup
  , get
  , getDefault
  , list
  , listByMode
    -- * Built-in Agents
  , defaultAgent
  , coderAgent
  , exploreAgent
  , researchAgent
  , planAgent
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Agent mode
data AgentMode 
  = Primary    -- Top-level agent
  | Subagent   -- Spawned by another agent

derive instance eqAgentMode :: Eq AgentMode

instance showAgentMode :: Show AgentMode where
  show Primary = "primary"
  show Subagent = "subagent"

-- | Agent definition
type Agent =
  { id :: String
  , name :: String
  , description :: String
  , mode :: AgentMode
  , systemPrompt :: String
  , tools :: Array String       -- Tool IDs this agent can use
  , maxTokens :: Int            -- Max response tokens
  , temperature :: Number       -- Model temperature
  }

-- | Agent configuration (for custom agents)
type AgentConfig =
  { id :: String
  , name :: String
  , description :: String
  , systemPrompt :: String
  , tools :: Maybe (Array String)
  , maxTokens :: Maybe Int
  , temperature :: Maybe Number
  }

-- ============================================================================
-- FFI
-- ============================================================================

-- | Load custom agents from config file
foreign import loadCustomAgentsFFI :: String -> Aff (Array Agent)

-- ============================================================================
-- BUILT-IN AGENTS
-- ============================================================================

-- | Default general-purpose agent
defaultAgent :: Agent
defaultAgent =
  { id: "default"
  , name: "Default Agent"
  , description: "General-purpose assistant for various tasks"
  , mode: Primary
  , systemPrompt: defaultSystemPrompt
  , tools: ["bash", "read", "write", "edit", "glob", "grep", "task", "webfetch", "question", "todowrite", "skill"]
  , maxTokens: 8192
  , temperature: 0.7
  }

-- | Code-focused agent
coderAgent :: Agent
coderAgent =
  { id: "coder"
  , name: "Coder Agent"
  , description: "Specialized for code writing and debugging"
  , mode: Primary
  , systemPrompt: coderSystemPrompt
  , tools: ["bash", "read", "write", "edit", "glob", "grep", "task", "lsp", "todowrite"]
  , maxTokens: 8192
  , temperature: 0.3  -- Lower temperature for more precise code
  }

-- | Fast exploration agent
exploreAgent :: Agent
exploreAgent =
  { id: "explore"
  , name: "Explore Agent"
  , description: "Fast agent for exploring codebases"
  , mode: Subagent
  , systemPrompt: exploreSystemPrompt
  , tools: ["read", "glob", "grep", "lsp"]  -- Read-only tools
  , maxTokens: 4096
  , temperature: 0.5
  }

-- | Research and analysis agent
researchAgent :: Agent
researchAgent =
  { id: "research"
  , name: "Research Agent"
  , description: "Research and analysis agent"
  , mode: Subagent
  , systemPrompt: researchSystemPrompt
  , tools: ["read", "webfetch", "websearch", "question"]
  , maxTokens: 8192
  , temperature: 0.7
  }

-- | Planning mode agent (read-only)
planAgent :: Agent
planAgent =
  { id: "plan"
  , name: "Plan Agent"
  , description: "Planning mode - research without making changes"
  , mode: Primary
  , systemPrompt: planSystemPrompt
  , tools: ["read", "glob", "grep", "webfetch", "question", "plan_exit"]  -- No write tools
  , maxTokens: 8192
  , temperature: 0.7
  }

-- | All built-in agents
builtInAgents :: Array Agent
builtInAgents = [defaultAgent, coderAgent, exploreAgent, researchAgent, planAgent]

-- ============================================================================
-- AGENT LOOKUP
-- ============================================================================

{-| Get an agent by ID.

Checks built-in agents first, then custom agents.
-}
get :: String -> Aff (Maybe Agent)
get agentId = do
  -- Check built-in agents
  case Array.find (\a -> a.id == agentId) builtInAgents of
    Just agent -> pure $ Just agent
    Nothing -> do
      -- Check custom agents
      customAgents <- loadCustomAgentsFFI ".forge/agents.json"
      pure $ Array.find (\a -> a.id == agentId) customAgents

{-| Get the default agent. -}
getDefault :: Aff (Maybe Agent)
getDefault = pure $ Just defaultAgent

{-| List all available agents. -}
list :: Aff (Either String (Array Agent))
list = do
  customAgents <- loadCustomAgentsFFI ".forge/agents.json"
  pure $ Right $ builtInAgents <> customAgents

{-| List agents by mode. -}
listByMode :: AgentMode -> Aff (Array Agent)
listByMode mode = do
  allAgents <- list
  case allAgents of
    Left _ -> pure []
    Right agents -> pure $ Array.filter (\a -> a.mode == mode) agents

-- ============================================================================
-- SYSTEM PROMPTS
-- ============================================================================

defaultSystemPrompt :: String
defaultSystemPrompt = """
You are Forge, an AI coding assistant. You help users with software engineering tasks including:
- Writing and debugging code
- Explaining code and concepts
- Refactoring and optimization
- Documentation

Be concise and focus on solving the user's problem. Use the available tools to explore the codebase and make changes.
"""

coderSystemPrompt :: String
coderSystemPrompt = """
You are Forge Coder, a specialized code assistant. Focus on:
- Writing clean, maintainable code
- Following best practices and patterns
- Comprehensive error handling
- Type safety where applicable

Be precise and minimize unnecessary changes. Always read files before editing them.
"""

exploreSystemPrompt :: String
exploreSystemPrompt = """
You are an exploration agent. Your job is to quickly find information in the codebase.
- Search efficiently using glob and grep
- Read relevant files
- Report findings concisely
- Do NOT make any changes

Return your findings in a structured format.
"""

researchSystemPrompt :: String
researchSystemPrompt = """
You are a research agent. Your job is to gather information and analyze it.
- Search the web for relevant information
- Read documentation and references
- Synthesize findings
- Provide evidence-based analysis

Focus on accuracy and cite your sources.
"""

planSystemPrompt :: String
planSystemPrompt = """
You are in planning mode. Your job is to research and create a plan WITHOUT making changes.
- Explore the codebase to understand the current state
- Identify what needs to change
- Create a detailed implementation plan
- Document dependencies and risks

When ready to implement, use the plan_exit tool to switch to build mode.
"""
