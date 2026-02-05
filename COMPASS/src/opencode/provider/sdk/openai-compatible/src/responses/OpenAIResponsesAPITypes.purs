{-|
Module      : Opencode.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesAPITypes
Description : OpenAI API type definitions
= OpenAI Responses API Types

Type definitions for OpenAI-compatible chat completion APIs.
Field names match the OpenAI API JSON format (snake_case).

== Type Safety

All types have EncodeJson/DecodeJson instances for API communication.
-}
module Opencode.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesAPITypes
  ( -- * Request Types
    ChatCompletionRequest(..)
  , ChatMessage(..)
  , ToolDefinition(..)
  , FunctionDefinition(..)
  , ToolCall(..)
  , FunctionCall(..)
    -- * Response Types
  , ChatCompletionResponse(..)
  , ChatChoice(..)
  , Usage(..)
    -- * Streaming Types
  , ChatCompletionChunk(..)
  , ChunkChoice(..)
  , Delta(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Argonaut 
  ( Json
  , class EncodeJson
  , class DecodeJson
  , encodeJson
  , decodeJson
  , (.:)
  , (.:?)
  , (~>)
  , (:=)
  , jsonEmptyObject
  )
import Data.Either (Either)
import Data.Generic.Rep (class Generic)

-- ════════════════════════════════════════════════════════════════════════════
-- REQUEST TYPES
-- ════════════════════════════════════════════════════════════════════════════

{-| Chat completion request. -}
type ChatCompletionRequest =
  { model :: String
  , messages :: Array ChatMessage
  , temperature :: Maybe Number
  , maxTokens :: Maybe Int
  , topP :: Maybe Number
  , frequencyPenalty :: Maybe Number
  , presencePenalty :: Maybe Number
  , stop :: Maybe (Array String)
  , stream :: Maybe Boolean
  , tools :: Maybe (Array ToolDefinition)
  , toolChoice :: Maybe String
  }

{-| Chat message. -}
type ChatMessage =
  { role :: String
  , content :: String
  , name :: Maybe String
  , tool_calls :: Maybe (Array ToolCall)
  , tool_call_id :: Maybe String
  }

{-| Tool definition. -}
type ToolDefinition =
  { "type" :: String
  , function :: FunctionDefinition
  }

{-| Function definition. -}
type FunctionDefinition =
  { name :: String
  , description :: Maybe String
  , parameters :: Json
  }

{-| Tool call in response. -}
type ToolCall =
  { id :: String
  , "type" :: String
  , function :: FunctionCall
  }

{-| Function call details. -}
type FunctionCall =
  { name :: String
  , arguments :: String
  }

-- ════════════════════════════════════════════════════════════════════════════
-- RESPONSE TYPES
-- ════════════════════════════════════════════════════════════════════════════

{-| Chat completion response. -}
type ChatCompletionResponse =
  { id :: String
  , object :: String
  , created :: Int
  , model :: String
  , choices :: Array ChatChoice
  , usage :: Maybe Usage
  }

{-| Response choice. -}
type ChatChoice =
  { index :: Int
  , message :: ChatMessage
  , finish_reason :: Maybe String
  }

{-| Token usage statistics. -}
type Usage =
  { prompt_tokens :: Int
  , completion_tokens :: Int
  , total_tokens :: Int
  }

-- ════════════════════════════════════════════════════════════════════════════
-- STREAMING TYPES
-- ════════════════════════════════════════════════════════════════════════════

{-| Streaming chunk response. -}
type ChatCompletionChunk =
  { id :: String
  , object :: String
  , created :: Int
  , model :: String
  , choices :: Array ChunkChoice
  }

{-| Streaming choice with delta. -}
type ChunkChoice =
  { index :: Int
  , delta :: Delta
  , finish_reason :: Maybe String
  }

{-| Delta content in streaming. -}
type Delta =
  { role :: Maybe String
  , content :: Maybe String
  , tool_calls :: Maybe (Array ToolCall)
  }
