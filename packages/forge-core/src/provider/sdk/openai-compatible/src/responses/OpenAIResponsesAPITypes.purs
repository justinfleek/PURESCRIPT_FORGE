-- | OpenAI Responses API Types
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/provider/sdk/openai-compatible/src/responses/openai-responses-api-types.ts
module Forge.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesAPITypes where

import Prelude
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | Chat completion request
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
  }

-- | Chat message
type ChatMessage =
  { role :: String
  , content :: String
  , name :: Maybe String
  , toolCalls :: Maybe (Array ToolCall)
  , toolCallId :: Maybe String
  }

-- | Tool definition
type ToolDefinition =
  { type :: String
  , function :: FunctionDefinition
  }

-- | Function definition
type FunctionDefinition =
  { name :: String
  , description :: Maybe String
  , parameters :: Foreign
  }

-- | Tool call
type ToolCall =
  { id :: String
  , type :: String
  , function :: FunctionCall
  }

-- | Function call
type FunctionCall =
  { name :: String
  , arguments :: String
  }

-- | Chat completion response
type ChatCompletionResponse =
  { id :: String
  , object :: String
  , created :: Int
  , model :: String
  , choices :: Array ChatChoice
  , usage :: Maybe UsageInfo
  }

-- | Chat choice
type ChatChoice =
  { index :: Int
  , message :: ChatMessage
  , finishReason :: Maybe String
  }

-- | Usage information
type UsageInfo =
  { promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  }
