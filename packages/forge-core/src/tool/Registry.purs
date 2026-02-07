{-|
Module      : Forge.Tool.Registry
Description : Tool registration and discovery
= Tool Registry

Central registry for all available tools. Handles tool registration,
discovery, and lookup by ID.

== Coeffect Equation

@
  register : ToolInfo -> Graded State Unit
  tools    : Model -> Agent -> Graded State (Array ToolDef)

  -- Requires:
  -- 1. State for maintaining registry
@

== Tool Lifecycle

1. Built-in tools are registered at startup
2. Plugin tools are loaded from config directories
3. Custom tools can be registered at runtime
4. Tools are filtered per agent permissions

== Built-in Tools

| ID          | Description                           |
|-------------|---------------------------------------|
| bash        | Execute shell commands (sandboxed)    |
| read        | Read file contents                    |
| write       | Write file contents                   |
| edit        | Edit file with replacements           |
| glob        | Find files by pattern                 |
| grep        | Search file contents                  |
| task        | Launch sub-agents                     |
| webfetch    | Fetch web content                     |
| search      | Web search via SearXNG                |
| question    | Ask user questions                    |
| todowrite   | Manage todo list                      |
| skill       | Load skill instructions               |
-}
module Forge.Tool.Registry
  ( -- * Registry Operations
    register
  , get
  , list
  , tools
    -- * Tool Types
  , ToolInfo
  , ToolDef
  , ToolResult
  , ToolContext
    -- * State
  , RegistryState
  , initialState
  , createRegistry
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Data.Either (Either(..))
import Data.Array as Array
import Data.Argonaut (Json, encodeJson)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Tool result type (for execute functions)
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

{-| Tool metadata for registration.

This is a simplified version for the registry state.
@
  record ToolInfo where
    id          : String
    description : String
@
-}
type ToolInfo =
  { id :: String
  , description :: String
  }

{-| Fully initialized tool definition.

Returned by `tools` after agent permission filtering and initialization.
-}
type ToolDef =
  { id :: String
  , description :: String
  , parameters :: Json
  , execute :: Json -> ToolContext -> Aff ToolResult
  }

{-| Registry state. -}
type RegistryState =
  { builtIn :: Array ToolInfo
  , custom :: Array ToolInfo
  }

-- ============================================================================
-- STATE
-- ============================================================================

-- | Initial registry state with built-in tools
initialState :: RegistryState
initialState =
  { builtIn:
      [ { id: "bash", description: "Execute shell commands in a sandboxed environment" }
      , { id: "read", description: "Read file contents" }
      , { id: "write", description: "Write content to a file" }
      , { id: "edit", description: "Edit file with string replacement" }
      , { id: "glob", description: "Find files by pattern" }
      , { id: "grep", description: "Search file contents" }
      , { id: "task", description: "Launch sub-agents for complex tasks" }
      , { id: "webfetch", description: "Fetch content from URLs" }
      , { id: "websearch", description: "Web search via search API" }
      , { id: "question", description: "Ask user questions" }
      , { id: "todowrite", description: "Update todo list" }
      , { id: "todoread", description: "Read todo list" }
      , { id: "skill", description: "Load skill instructions" }
      , { id: "lsp", description: "Language Server Protocol operations" }
      , { id: "list", description: "List directory contents" }
      , { id: "plan_exit", description: "Switch from plan mode to build mode" }
      , { id: "plan_enter", description: "Switch from build mode to plan mode" }
      ]
  , custom: []
  }

-- | Create a new registry ref
createRegistry :: Effect (Ref RegistryState)
createRegistry = Ref.new initialState

-- ============================================================================
-- REGISTRY OPERATIONS
-- ============================================================================

{-| Register a custom tool.

If a tool with the same ID exists, it is replaced.
-}
register :: ToolInfo -> Ref RegistryState -> Effect Unit
register tool stateRef = do
  state <- Ref.read stateRef
  let existing = Array.findIndex (\t -> t.id == tool.id) state.custom
  let newCustom = case existing of
        Just idx -> Array.updateAt idx tool state.custom # fromMaybe state.custom
        Nothing -> Array.snoc state.custom tool
  Ref.write state { custom = newCustom } stateRef

{-| Get a tool by ID. -}
get :: String -> Ref RegistryState -> Effect (Maybe ToolInfo)
get toolId stateRef = do
  state <- Ref.read stateRef
  let all = state.builtIn <> state.custom
  pure $ Array.find (\t -> t.id == toolId) all

{-| List all registered tools. -}
list :: Ref RegistryState -> Effect (Array ToolInfo)
list stateRef = do
  state <- Ref.read stateRef
  pure $ state.builtIn <> state.custom

{-| Get tools available for a model/agent combination.

Filters tools based on:
1. Agent permissions
2. Model capabilities
3. Feature flags
-}
tools :: { providerID :: String, modelID :: String } -> Maybe String -> Ref RegistryState -> Aff (Array ToolInfo)
tools model agentId stateRef = do
  -- Get all registered tools
  allTools <- liftEffect $ list stateRef
  
  -- Filter by agent permissions (if agentId provided)
  let filteredByAgent = case agentId of
        Nothing -> allTools
        Just agent -> filterToolsByAgent agent allTools
  
  -- Filter by model capabilities
  modelSupports <- checkModelSupportsTools model
  let filteredByModel = if modelSupports
        then filteredByAgent
        else [] -- If model doesn't support tools, return empty
  
  pure filteredByModel

-- | Filter tools by agent permissions
-- | Different agent types have different tool access levels
filterToolsByAgent :: String -> Array ToolInfo -> Array ToolInfo
filterToolsByAgent agent allTools = 
  case agent of
    "restricted" -> Array.filter (\t -> not (isRestrictedTool t.id)) allTools
    "explore" -> Array.filter (\t -> isExplorationTool t.id) allTools
    "research" -> Array.filter (\t -> isResearchTool t.id) allTools
    "general" -> allTools -- General agent has access to all tools
    _ -> allTools -- Default: allow all tools

-- | Check if a tool is restricted (dangerous operations)
isRestrictedTool :: String -> Boolean
isRestrictedTool toolId = 
  toolId == "bash" || 
  toolId == "write" || 
  toolId == "edit" || 
  toolId == "multiedit" ||
  toolId == "task"

-- | Check if a tool is suitable for exploration agent
isExplorationTool :: String -> Boolean
isExplorationTool toolId =
  toolId == "read" ||
  toolId == "grep" ||
  toolId == "glob" ||
  toolId == "list" ||
  toolId == "codesearch" ||
  toolId == "lsp" ||
  toolId == "todoread"

-- | Check if a tool is suitable for research agent
isResearchTool :: String -> Boolean
isResearchTool toolId =
  toolId == "read" ||
  toolId == "websearch" ||
  toolId == "webfetch" ||
  toolId == "codesearch" ||
  toolId == "question"

-- | Check if model supports tools
-- | In production, this would query the provider registry
-- | For now, we check known providers/models or default to true
checkModelSupportsTools :: { providerID :: String, modelID :: String } -> Aff Boolean
checkModelSupportsTools model = do
  -- Known models that don't support tools (legacy models)
  let unsupportedModels = 
        [ "gpt-3.5-turbo"  -- Older GPT-3.5 models may not support tools
        , "text-davinci-003"
        ]
  
  -- Check if this is a known unsupported model
  let isUnsupported = Array.elem model.modelID unsupportedModels
  
  -- Most modern models support tools, so default to true
  -- In production, this would query ProviderRegistry.getModel
  pure $ not isUnsupported
