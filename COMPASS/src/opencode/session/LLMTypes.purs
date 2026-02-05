{-|
Module      : Opencode.Session.LLMTypes
Description : Type definitions for LLM API interaction
= LLM Types

Extracted from LLM.purs to comply with 500-line file limit.
Contains all type definitions for OpenAI-compatible chat completions.

== Coeffect Equation

@
  LLMRequest  : Model × Messages × Config -> Request
  LLMResponse : Response -> Choices × Usage
  ToolCall    : ID × Function × Arguments -> ToolInvocation
@

-}
module Opencode.Session.LLMTypes
  ( -- * Core Types
    Role(..)
  , ContentPart(..)
  , LLMMessage
  , ToolCall
  , ToolFunction
  , ToolDefinition
  , FunctionDefinition
    -- * Request/Response
  , LLMRequest
  , ToolChoice(..)
  , LLMResponse
  , Choice
  , FinishReason(..)
  , LLMUsage
    -- * Streaming
  , StreamChunk
  , Delta
  , StreamHandler
    -- * Configuration
  , ProviderConfig
  , defaultProviderConfig
    -- * API Types
  , APIMessage
  , APIToolCall
  , APIToolDefinition
  , APIResponse
  , APIChoice
  , APIUsage
  , APIChatRequest
  , APIStreamChunk
  , APIChunkChoice
  , APIDelta
    -- * Helpers
  , showRole
  , parseRole
  , parseFinishReason
  , defaultUsage
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Argonaut (Json)
import Effect.Aff (Aff)

-- ════════════════════════════════════════════════════════════════════════════
-- CORE TYPES
-- ════════════════════════════════════════════════════════════════════════════

-- | LLM message role (matches OpenAI)
data Role
  = System
  | User
  | Assistant
  | Tool

derive instance eqRole :: Eq Role

instance showRoleInstance :: Show Role where
  show = showRole

-- | Show role as string
showRole :: Role -> String
showRole = case _ of
  System -> "system"
  User -> "user"
  Assistant -> "assistant"
  Tool -> "tool"

-- | Parse role string to Role
parseRole :: String -> Role
parseRole = case _ of
  "system" -> System
  "user" -> User
  "assistant" -> Assistant
  "tool" -> Tool
  _ -> User

-- | LLM message content
data ContentPart
  = TextPart String
  | ImagePart { url :: String, detail :: Maybe String }
  | ToolResultPart { toolCallId :: String, content :: String }

-- | LLM message
type LLMMessage =
  { role :: Role
  , content :: Array ContentPart
  , name :: Maybe String
  , toolCalls :: Maybe (Array ToolCall)
  , toolCallId :: Maybe String
  }

-- | Tool call in assistant response
type ToolCall =
  { id :: String
  , type :: String
  , function :: ToolFunction
  }

-- | Tool function definition
type ToolFunction =
  { name :: String
  , arguments :: String
  }

-- | Tool definition for API
type ToolDefinition =
  { type :: String
  , function :: FunctionDefinition
  }

-- | Function definition
type FunctionDefinition =
  { name :: String
  , description :: String
  , parameters :: Json
  }

-- ════════════════════════════════════════════════════════════════════════════
-- REQUEST/RESPONSE TYPES
-- ════════════════════════════════════════════════════════════════════════════

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
  = Auto
  | None
  | Required
  | Specific String

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
  = Stop
  | ToolCalls
  | Length
  | ContentFilter

-- | Parse finish reason string
parseFinishReason :: String -> FinishReason
parseFinishReason = case _ of
  "stop" -> Stop
  "tool_calls" -> ToolCalls
  "length" -> Length
  "content_filter" -> ContentFilter
  _ -> Stop

-- | LLM usage stats
type LLMUsage =
  { promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cacheHit :: Maybe Int
  , cacheWrite :: Maybe Int
  }

-- | Default usage when none provided
defaultUsage :: LLMUsage
defaultUsage =
  { promptTokens: 0
  , completionTokens: 0
  , totalTokens: 0
  , cacheHit: Nothing
  , cacheWrite: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
-- STREAMING TYPES
-- ════════════════════════════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════════════════════════════
-- CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

-- | Provider configuration for LLM calls
type ProviderConfig =
  { baseUrl :: String
  , apiKey :: String
  , providerId :: String
  , headers :: Array { key :: String, value :: String }
  , timeout :: Int
  }

-- | Default provider configuration (uses environment)
defaultProviderConfig :: ProviderConfig
defaultProviderConfig =
  { baseUrl: "https://api.openai.com/v1"
  , apiKey: ""
  , providerId: "openai"
  , headers: []
  , timeout: 120000
  }

-- ════════════════════════════════════════════════════════════════════════════
-- API WIRE TYPES (OpenAI format)
-- ════════════════════════════════════════════════════════════════════════════

-- | API-level chat message
type APIMessage =
  { role :: String
  , content :: String
  , name :: Maybe String
  , tool_calls :: Maybe (Array APIToolCall)
  , tool_call_id :: Maybe String
  }

-- | API-level tool call
type APIToolCall =
  { id :: String
  , "type" :: String
  , function :: { name :: String, arguments :: String }
  }

-- | API-level tool definition
type APIToolDefinition =
  { "type" :: String
  , function :: { name :: String, description :: Maybe String, parameters :: Json }
  }

-- | API response type
type APIResponse =
  { id :: String
  , object :: String
  , created :: Int
  , model :: String
  , choices :: Array APIChoice
  , usage :: Maybe APIUsage
  }

type APIChoice =
  { index :: Int
  , message :: APIMessage
  , finish_reason :: Maybe String
  }

type APIUsage =
  { prompt_tokens :: Int
  , completion_tokens :: Int
  , total_tokens :: Int
  }

-- | API request type for chat completion
type APIChatRequest =
  { model :: String
  , messages :: Array APIMessage
  , temperature :: Maybe Number
  , maxTokens :: Maybe Int
  , topP :: Maybe Number
  , frequencyPenalty :: Maybe Number
  , presencePenalty :: Maybe Number
  , stop :: Maybe (Array String)
  , stream :: Maybe Boolean
  , tools :: Maybe (Array APIToolDefinition)
  , toolChoice :: Maybe String
  }

-- | API streaming chunk type
type APIStreamChunk =
  { id :: String
  , object :: String
  , created :: Int
  , model :: String
  , choices :: Array APIChunkChoice
  }

type APIChunkChoice =
  { index :: Int
  , delta :: APIDelta
  , finish_reason :: Maybe String
  }

type APIDelta =
  { role :: Maybe String
  , content :: Maybe String
  , tool_calls :: Maybe (Array APIToolCall)
  }
