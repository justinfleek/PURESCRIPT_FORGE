{-|
Module      : Tool.Registry
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
module Tool.Registry
  ( -- * Registry Operations
    register
  , get
  , list
  , tools
    -- * Tool Types
  , ToolInfo(..)
  , ToolDef(..)
    -- * State
  , RegistryState(..)
  , initialState
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.Argonaut (Json, class EncodeJson, encodeJson)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo as FullToolInfo, ToolMetadata(..), ErrorMetadata)
import Tool.Dispatcher (getToolExecute, toolRegistry)

-- ============================================================================
-- TYPES
-- ============================================================================

{-| Tool metadata for registration.

This is a simplified version for the registry state.
The full ToolInfo with execute function is stored separately.
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

-- | Full tool registry mapping IDs to full tool info with execute functions
-- | In production, this would be a proper registry service
type FullToolRegistry = Map String FullToolInfo

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
      , { id: "search", description: "Web search via SearXNG" }
      , { id: "question", description: "Ask user questions" }
      , { id: "todowrite", description: "Update todo list" }
      , { id: "todoread", description: "Read todo list" }
      , { id: "skill", description: "Load skill instructions" }
      ]
  , custom: []
  }

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
  where
    fromMaybe :: forall a. a -> Maybe a -> a
    fromMaybe def Nothing = def
    fromMaybe _ (Just x) = x

{-| Get a tool by ID. -}
get :: String -> Ref RegistryState -> Effect (Maybe ToolInfo)
get id stateRef = do
  state <- Ref.read stateRef
  let all = state.builtIn <> state.custom
  pure $ Array.find (\t -> t.id == id) all

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
tools :: { providerID :: String, modelID :: String } -> Maybe String -> Ref RegistryState -> Aff (Array ToolDef)
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
  
  -- Convert to ToolDef format using Tool.Dispatcher
  let toolDefs = Array.mapMaybe (\tool -> do
        executeFn <- getToolExecute tool.id
        toolInfo <- Map.lookup tool.id toolRegistry
        pure
          { id: tool.id
          , description: tool.description
          , parameters: toolInfo.parameters
          , execute: executeFn
          }
      ) filteredByModel
  
  pure toolDefs
  where
    liftEffect :: forall a. Effect a -> Aff a
    liftEffect = Effect.Class.liftEffect
    
    -- Filter tools by agent permissions
    -- Different agent types have different tool access levels
    filterToolsByAgent :: String -> Array ToolInfo -> Array ToolInfo
    filterToolsByAgent agent tools = 
      case agent of
        "restricted" -> Array.filter (\t -> not (isRestrictedTool t.id)) tools
        "explore" -> Array.filter (\t -> isExplorationTool t.id) tools
        "research" -> Array.filter (\t -> isResearchTool t.id) tools
        "general" -> tools -- General agent has access to all tools
        _ -> tools -- Default: allow all tools
    
    -- Check if a tool is restricted (dangerous operations)
    isRestrictedTool :: String -> Boolean
    isRestrictedTool toolId = 
      toolId == "bash" || 
      toolId == "write" || 
      toolId == "edit" || 
      toolId == "multiedit" ||
      toolId == "task"
    
    -- Check if a tool is suitable for exploration agent
    isExplorationTool :: String -> Boolean
    isExplorationTool toolId =
      toolId == "read" ||
      toolId == "grep" ||
      toolId == "glob" ||
      toolId == "list" ||
      toolId == "codesearch" ||
      toolId == "lsp" ||
      toolId == "todoread"
    
    -- Check if a tool is suitable for research agent
    isResearchTool :: String -> Boolean
    isResearchTool toolId =
      toolId == "read" ||
      toolId == "search" ||
      toolId == "websearch" ||
      toolId == "webfetch" ||
      toolId == "codesearch" ||
      toolId == "question"
    
    -- Check if model supports tools
    -- In production, this would query the provider registry
    -- For now, we check known providers/models or default to true
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
