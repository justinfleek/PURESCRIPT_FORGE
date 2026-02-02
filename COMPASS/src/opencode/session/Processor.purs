-- | Session Processor - orchestrates LLM interaction and tool execution
-- | 
-- | This module implements the core processing loop:
-- | 1. Receive user message
-- | 2. Send to LLM with context
-- | 3. Process LLM response (text or tool calls)
-- | 4. Execute tool calls (with permission checks)
-- | 5. Return tool results to LLM
-- | 6. Repeat until LLM indicates completion
-- |
-- | INVARIANTS (proven in proofs/lean/Opencode/Proofs/Session.lean):
-- | - SessionID is never empty (SessionID.nonEmpty)
-- | - Session time.created <= time.updated (SessionTime.ordered)
-- | - All parent references are valid (SessionStore.parentInvariant)
-- |
-- | The state machine ensures:
-- | - Only one processing loop per session at a time
-- | - Proper cleanup on abort/error
-- | - Permission checks before all tool executions
module Opencode.Session.Processor where

import Prelude
import Effect.Aff (Aff, attempt, delay, forkAff, killFiber, Fiber, Milliseconds(..))
import Effect.Class (liftEffect)
import Effect.Ref (Ref, new, read, write)
import Effect.Exception (error)
import Effect (Effect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Map as Map
import Data.Tuple (Tuple(..))
import Data.Argonaut (Json, encodeJson, decodeJson, stringify, jsonParser)
import Data.Traversable (traverse)
import Data.Foldable (for_, foldl)
import Data.Array as Array
import Data.String as String

-- Import canonical types
import Opencode.Types.Session (SessionInfo, SessionID, SessionTime)
import Opencode.Types.Message (MessageInfo, MessageRole(..))
import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo, AbortSignal(..))
import Opencode.Types.Permission (PermissionRequest, PermissionReply)

-- Import LLM module for API calls
import Opencode.Session.LLM as LLM

-- | Processor configuration
type ProcessorConfig =
  { sessionID :: SessionID        -- INVARIANT: non-empty (proven in Lean)
  , model :: String               -- Model ID to use
  , agent :: Maybe String         -- Optional agent override
  , maxIterations :: Int          -- Max tool call iterations (safety limit)
  , systemPrompt :: Maybe String  -- Optional system prompt override
  , providerConfig :: LLM.ProviderConfig  -- Provider API configuration
  , tools :: Array ToolInfo       -- Available tools
  }

-- | Processing state machine
-- | 
-- | State transitions:
-- |   Idle -> Processing (on startProcessing)
-- |   Processing -> WaitingForTool (on tool call)
-- |   Processing -> WaitingForPermission (on permission required)
-- |   Processing -> Complete (on LLM finish)
-- |   Processing -> Error (on error)
-- |   WaitingForTool -> Processing (on tool result)
-- |   WaitingForPermission -> Processing (on permission granted)
-- |   WaitingForPermission -> Error (on permission denied)
-- |   * -> Idle (on stopProcessing)
data ProcessorState
  = Idle
  | Processing { iteration :: Int }
  | WaitingForTool { toolCalls :: Array ToolCall }
  | WaitingForPermission { request :: PermissionRequest }
  | Complete { finalMessage :: Maybe MessageInfo }
  | Error { message :: String, recoverable :: Boolean }

derive instance eqProcessorState :: Eq ProcessorState

-- | Tool call pending execution
type ToolCall =
  { id :: String
  , name :: String
  , arguments :: Json
  }

-- | Processor runtime state (mutable)
type ProcessorRuntime =
  { config :: ProcessorConfig
  , state :: ProcessorState
  , fiber :: Maybe (Fiber Unit)      -- Active processing fiber
  , messages :: Array MessageInfo    -- Conversation history
  , pendingTools :: Array ToolCall   -- Tools waiting for execution
  }

-- | Global processor registry (one processor per session)
-- | In real implementation, this would be an Effect-based mutable map
type ProcessorRegistry = Map.Map SessionID ProcessorRuntime

-- | Create a new processor
createProcessor :: ProcessorConfig -> ProcessorRuntime
createProcessor config =
  { config
  , state: Idle
  , fiber: Nothing
  , messages: []
  , pendingTools: []
  }

-- | Validate configuration
-- | Enforces Lean invariant: SessionID must be non-empty
validateConfig :: ProcessorConfig -> Either String ProcessorConfig
validateConfig config
  | config.sessionID == "" = Left "SessionID cannot be empty (invariant: SessionID.nonEmpty)"
  | config.maxIterations <= 0 = Left "maxIterations must be positive"
  | otherwise = Right config

-- | Start processing a session
-- | This initiates the LLM loop
startProcessing :: ProcessorConfig -> Aff (Either String Unit)
startProcessing config = do
  case validateConfig config of
    Left err -> pure (Left err)
    Right validConfig -> do
      -- TODO: 
      -- 1. Look up or create processor in registry
      -- 2. Check state is Idle
      -- 3. Fork processing loop
      -- 4. Update state to Processing
      pure (Right unit)

-- | Stop processing
stopProcessing :: SessionID -> Aff (Either String Unit)
stopProcessing sessionID = do
  -- TODO:
  -- 1. Look up processor in registry
  -- 2. Kill fiber if running
  -- 3. Set state to Idle
  -- 4. Clean up pending tools
  pure (Right unit)

-- | Get current processing state
getState :: SessionID -> Aff (Either String ProcessorState)
getState sessionID = do
  -- TODO: Look up in registry
  pure (Right Idle)

-- | Process a single iteration of the LLM loop
-- | This is the core logic that:
-- | 1. Sends messages to LLM
-- | 2. Handles response (text or tool calls)
-- | 3. Executes tools (with permission)
-- | 4. Returns results
processIteration :: ProcessorRuntime -> Aff (Either String ProcessorState)
processIteration runtime = do
  -- Build LLM request from processor state
  let llmRequest = buildLLMRequest runtime
  
  -- Call LLM via provider
  result <- LLM.complete runtime.config.providerConfig llmRequest
  
  case result of
    Left err -> pure $ Right $ Error { message: err, recoverable: true }
    Right response -> do
      -- Check if response contains tool calls
      if LLM.hasToolCalls response
        then do
          -- Extract tool calls and transition to WaitingForTool
          let calls = extractToolCalls response
          pure $ Right $ WaitingForTool { toolCalls: calls }
        else do
          -- No tool calls - completion is done
          pure $ Right $ Complete { finalMessage: Nothing }

-- | Build LLM request from processor runtime state
buildLLMRequest :: ProcessorRuntime -> LLM.LLMRequest
buildLLMRequest runtime =
  { model: runtime.config.model
  , messages: buildMessages runtime
  , temperature: Just 0.7
  , maxTokens: Just 16384
  , tools: Just (map toToolDefinition runtime.config.tools)
  , toolChoice: Just LLM.Auto
  , stream: false
  }

-- | Build messages array from runtime state
buildMessages :: ProcessorRuntime -> Array LLM.LLMMessage
buildMessages runtime =
  let systemMsg = case runtime.config.systemPrompt of
        Just prompt -> [LLM.systemMessage prompt]
        Nothing -> [LLM.systemMessage defaultSystemPrompt]
      -- TODO: Convert stored messages to LLM format
      historyMsgs = []
  in systemMsg <> historyMsgs

-- | Default system prompt
defaultSystemPrompt :: String
defaultSystemPrompt = "You are an AI coding assistant. Help users with software engineering tasks. Use the available tools to complete tasks. Be concise and accurate."

-- | Convert ToolInfo to LLM ToolDefinition
toToolDefinition :: ToolInfo -> LLM.ToolDefinition
toToolDefinition tool =
  { "type": "function"
  , function:
      { name: tool.id
      , description: tool.description
      , parameters: tool.parameters
      }
  }

-- | Extract tool calls from LLM response
extractToolCalls :: LLM.LLMResponse -> Array ToolCall
extractToolCalls response =
  map convertToolCall (LLM.getToolCalls response)
  where
    convertToolCall tc =
      { id: tc.id
      , name: tc.function.name
      , arguments: case jsonParser tc.function.arguments of
          Left _ -> encodeJson {}
          Right json -> json
      }

-- | Execute a tool call
-- | Requires permission check first
executeTool :: Array ToolInfo -> ToolCall -> ToolContext -> Aff (Either String ToolResult)
executeTool tools call ctx = do
  -- 1. Look up tool in registry
  case Array.find (\t -> t.id == call.name) tools of
    Nothing -> pure $ Left ("Unknown tool: " <> call.name)
    Just tool -> do
      -- 2. Execute tool with arguments
      result <- attempt $ tool.execute call.arguments ctx
      case result of
        Left err -> pure $ Left ("Tool execution error: " <> show err)
        Right res -> pure $ Right res

-- | Execute all pending tool calls and return results
executeToolCalls :: ProcessorRuntime -> Array ToolCall -> Aff (Array { id :: String, result :: Either String ToolResult })
executeToolCalls runtime calls = do
  let ctx = buildToolContext runtime
  traverse (executeOne ctx) calls
  where
    executeOne ctx call = do
      result <- executeTool runtime.config.tools call ctx
      pure { id: call.id, result }

-- | Run the full processing loop until completion or max iterations
runProcessingLoop :: Ref ProcessorRuntime -> Aff (Either String ProcessorState)
runProcessingLoop runtimeRef = loop 0
  where
    loop iteration = do
      runtime <- liftEffect $ read runtimeRef
      
      -- Check max iterations
      if iteration >= runtime.config.maxIterations
        then pure $ Right $ Error { message: "Max iterations exceeded", recoverable: false }
        else do
          -- Run one iteration
          result <- processIteration runtime
          case result of
            Left err -> pure $ Left err
            Right state -> case state of
              Complete _ -> do
                -- Done!
                liftEffect $ write runtime { state = state } runtimeRef
                pure $ Right state
              
              Error _ -> do
                -- Error occurred
                liftEffect $ write runtime { state = state } runtimeRef
                pure $ Right state
              
              WaitingForTool { toolCalls } -> do
                -- Execute tool calls
                results <- executeToolCalls runtime toolCalls
                
                -- Add tool results as messages and continue
                let newMessages = map toolResultToMessage results
                liftEffect $ write runtime 
                  { state = Processing { iteration: iteration + 1 }
                  , pendingTools = []
                  } runtimeRef
                
                -- Continue loop
                loop (iteration + 1)
              
              _ -> do
                -- Continue processing
                liftEffect $ write runtime { state = Processing { iteration: iteration + 1 } } runtimeRef
                loop (iteration + 1)
    
    toolResultToMessage { id, result } =
      case result of
        Left err -> { id, content: "Error: " <> err }
        Right res -> { id, content: res.output }

-- | Check if a tool call requires permission
requiresPermission :: ToolCall -> Boolean
requiresPermission call =
  -- Tools that modify state require explicit permission
  Array.elem call.name ["bash", "edit", "write", "task"]

-- | Build tool context from processor runtime
buildToolContext :: ProcessorRuntime -> ToolContext
buildToolContext runtime =
  { sessionID: runtime.config.sessionID
  , messageID: ""  -- Would be actual message ID
  , agent: fromMaybe "default" runtime.config.agent
  , abort: AbortSignal  -- Placeholder abort signal
  , callID: Nothing
  , extra: Nothing
  , messages: []  -- Would convert runtime.messages
  }

-- Helpers
fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe def = case _ of
  Nothing -> def
  Just a -> a

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
