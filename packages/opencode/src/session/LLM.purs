-- | Session LLM - language model interaction
-- | 
-- | This module handles communication with language model providers.
-- | It implements the OpenAI-compatible API interface and handles:
-- | - Message formatting (system, user, assistant, tool)
-- | - Tool definitions and invocations
-- | - Streaming responses
-- | - Token usage tracking
-- |
-- | PROTOCOL (proven in proofs/lean/Bridge/Protocol/JsonRpc.lean):
-- | - All requests/responses follow JSON-RPC 2.0 format
-- | - Tool calls follow OpenAI function calling schema
-- |
-- | WebSocket state machine (proven in proofs/lean/Bridge/Protocol/WebSocket.lean):
-- | - Connection states: Connecting -> Open -> Closing -> Closed
-- | - Messages only sent in Open state
module Opencode.Session.LLM where

import Prelude
import Effect.Aff (Aff, attempt, makeAff, Canceler(..))
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.Argonaut (Json, encodeJson, decodeJson)
import Data.Traversable (traverse)

-- Import canonical types
import Opencode.Types.Message (MessageRole(..), TokenUsage)
import Opencode.Types.Provider (ModelInfo, ProviderInfo)

-- | LLM message role (matches OpenAI)
data Role
  = System
  | User
  | Assistant
  | Tool

derive instance eqRole :: Eq Role

instance showRole :: Show Role where
  show = case _ of
    System -> "system"
    User -> "user"
    Assistant -> "assistant"
    Tool -> "tool"

-- | LLM message content
-- | Can be text or structured content (for images, etc.)
data ContentPart
  = TextPart String
  | ImagePart { url :: String, detail :: Maybe String }
  | ToolResultPart { toolCallId :: String, content :: String }

-- | LLM message
type LLMMessage =
  { role :: Role
  , content :: Array ContentPart
  , name :: Maybe String         -- For tool role messages
  , toolCalls :: Maybe (Array ToolCall)  -- For assistant messages with tool calls
  , toolCallId :: Maybe String   -- For tool role messages
  }

-- | Tool call in assistant response
type ToolCall =
  { id :: String
  , type :: String  -- Always "function"
  , function :: ToolFunction
  }

-- | Tool function definition
type ToolFunction =
  { name :: String
  , arguments :: String  -- JSON string
  }

-- | Tool definition for API
type ToolDefinition =
  { type :: String  -- Always "function"
  , function :: FunctionDefinition
  }

-- | Function definition
type FunctionDefinition =
  { name :: String
  , description :: String
  , parameters :: Json  -- JSON Schema
  }

-- | LLM request
type LLMRequest =
  { model :: String
  , messages :: Array LLMMessage
  , temperature :: Maybe Number
  , maxTokens :: Maybe Int
  , tools :: Maybe (Array ToolDefinition)
  , toolChoice :: Maybe ToolChoice
  , stream :: Boolean
  }

-- | Tool choice configuration
data ToolChoice
  = Auto           -- Let model decide
  | None           -- Don't use tools
  | Required       -- Must use a tool
  | Specific String  -- Use specific tool

-- | LLM response
type LLMResponse =
  { id :: String
  , model :: String
  , choices :: Array Choice
  , usage :: LLMUsage
  }

-- | Response choice
type Choice =
  { index :: Int
  , message :: LLMMessage
  , finishReason :: FinishReason
  }

-- | Why the model stopped generating
data FinishReason
  = Stop           -- Natural stop
  | ToolCalls      -- Model wants to call tools
  | Length         -- Hit max tokens
  | ContentFilter  -- Content was filtered

-- | LLM usage stats
type LLMUsage =
  { promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cacheHit :: Maybe Int      -- Cached tokens (if supported)
  , cacheWrite :: Maybe Int    -- Tokens written to cache
  }

-- | Streaming chunk
type StreamChunk =
  { id :: String
  , model :: String
  , delta :: Delta
  , finishReason :: Maybe FinishReason
  }

-- | Streaming delta
type Delta =
  { role :: Maybe Role
  , content :: Maybe String
  , toolCalls :: Maybe (Array ToolCall)
  }

-- | Stream handler callbacks
type StreamHandler =
  { onChunk :: StreamChunk -> Aff Unit
  , onDone :: LLMUsage -> Aff Unit
  , onError :: String -> Aff Unit
  }

-- | Send a non-streaming request to the LLM
complete :: LLMRequest -> Aff (Either String LLMResponse)
complete request = do
  -- TODO:
  -- 1. Build HTTP request
  -- 2. Send to provider endpoint
  -- 3. Parse response
  -- 4. Handle errors
  pure (Left "Not implemented: LLM.complete")

-- | Stream a completion from the LLM
-- | Returns a Canceler to stop the stream
stream :: LLMRequest -> StreamHandler -> Aff (Either String (Aff Unit))
stream request handler = do
  -- TODO:
  -- 1. Build HTTP request with stream: true
  -- 2. Open SSE connection
  -- 3. Parse chunks and call handler.onChunk
  -- 4. On [DONE], call handler.onDone
  -- 5. Return canceler
  pure (Left "Not implemented: LLM.stream")

-- | Create a simple user message
userMessage :: String -> LLMMessage
userMessage content =
  { role: User
  , content: [TextPart content]
  , name: Nothing
  , toolCalls: Nothing
  , toolCallId: Nothing
  }

-- | Create a system message
systemMessage :: String -> LLMMessage
systemMessage content =
  { role: System
  , content: [TextPart content]
  , name: Nothing
  , toolCalls: Nothing
  , toolCallId: Nothing
  }

-- | Create a tool result message
toolResultMessage :: String -> String -> LLMMessage
toolResultMessage callId result =
  { role: Tool
  , content: [ToolResultPart { toolCallId: callId, content: result }]
  , name: Nothing
  , toolCalls: Nothing
  , toolCallId: Just callId
  }

-- | Check if response contains tool calls
hasToolCalls :: LLMResponse -> Boolean
hasToolCalls response =
  case Array.head response.choices of
    Nothing -> false
    Just choice -> case choice.message.toolCalls of
      Nothing -> false
      Just calls -> not (Array.null calls)

-- | Extract tool calls from response
getToolCalls :: LLMResponse -> Array ToolCall
getToolCalls response =
  case Array.head response.choices of
    Nothing -> []
    Just choice -> fromMaybe [] choice.message.toolCalls

-- | Calculate total tokens used
totalTokens :: LLMUsage -> Int
totalTokens usage = usage.promptTokens + usage.completionTokens

-- Helpers
fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe def = case _ of
  Nothing -> def
  Just a -> a

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
