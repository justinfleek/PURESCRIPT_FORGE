-- | Provider Transform utilities
-- | Ported from: opencode-dev/packages/opencode/src/provider/transform.ts
module Forge.Provider.Transform 
  ( -- * Types
    ProviderFormat(..)
  , TransformResult
  , CommonMessage
  , CommonContentPart
  , CommonToolCall
  , CommonRequest
  , CommonResponse
  , CommonChunk
  , MessageRole(..)
  , FinishReason(..)
    -- * Transform Functions
  , parseProviderFormat
  , transformRequest
  , transformResponse
  , transformChunk
  , normalizeUsage
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Argonaut (Json)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Provider format
data ProviderFormat
  = Anthropic
  | OpenAI
  | OACompat
  | Google
  | Bedrock

derive instance eqProviderFormat :: Eq ProviderFormat

instance showProviderFormat :: Show ProviderFormat where
  show Anthropic = "anthropic"
  show OpenAI = "openai"
  show OACompat = "oa-compat"
  show Google = "google"
  show Bedrock = "bedrock"

-- | Parse provider format from string
parseProviderFormat :: String -> Maybe ProviderFormat
parseProviderFormat s = case String.toLower s of
  "anthropic" -> Just Anthropic
  "openai" -> Just OpenAI
  "oa-compat" -> Just OACompat
  "oacompat" -> Just OACompat
  "google" -> Just Google
  "bedrock" -> Just Bedrock
  "amazon-bedrock" -> Just Bedrock
  _ -> Nothing

-- | Message role
data MessageRole
  = System
  | User
  | Assistant
  | Tool

derive instance eqMessageRole :: Eq MessageRole

instance showMessageRole :: Show MessageRole where
  show System = "system"
  show User = "user"
  show Assistant = "assistant"
  show Tool = "tool"

parseMessageRole :: String -> Maybe MessageRole
parseMessageRole "system" = Just System
parseMessageRole "user" = Just User
parseMessageRole "assistant" = Just Assistant
parseMessageRole "tool" = Just Tool
parseMessageRole _ = Nothing

-- | Finish reason
data FinishReason
  = Stop
  | ToolCalls
  | Length
  | ContentFilter
  | MaxTokens
  | EndTurn

derive instance eqFinishReason :: Eq FinishReason

instance showFinishReason :: Show FinishReason where
  show Stop = "stop"
  show ToolCalls = "tool_calls"
  show Length = "length"
  show ContentFilter = "content_filter"
  show MaxTokens = "max_tokens"
  show EndTurn = "end_turn"

parseFinishReason :: String -> Maybe FinishReason
parseFinishReason "stop" = Just Stop
parseFinishReason "tool_calls" = Just ToolCalls
parseFinishReason "length" = Just Length
parseFinishReason "content_filter" = Just ContentFilter
parseFinishReason "max_tokens" = Just MaxTokens
parseFinishReason "end_turn" = Just EndTurn
parseFinishReason _ = Nothing

-- | Content part type
data ContentPartType
  = TextPart
  | ImageUrlPart
  | ImageBase64Part
  | ToolUsePart
  | ToolResultPart

derive instance eqContentPartType :: Eq ContentPartType

-- | Common content part
type CommonContentPart =
  { partType :: ContentPartType
  , text :: Maybe String
  , imageUrl :: Maybe String
  , imageBase64 :: Maybe String
  , mimeType :: Maybe String
  , toolUseId :: Maybe String
  , toolName :: Maybe String
  , toolInput :: Maybe String
  , toolResult :: Maybe String
  }

-- | Common tool call
type CommonToolCall =
  { id :: String
  , toolType :: String  -- "function"
  , functionName :: String
  , functionArguments :: String
  }

-- | Common tool definition
type CommonTool =
  { toolType :: String  -- "function"
  , functionName :: String
  , functionDescription :: Maybe String
  , functionParameters :: Maybe Json
  }

-- | Common message
type CommonMessage =
  { role :: MessageRole
  , content :: Maybe String
  , contentParts :: Maybe (Array CommonContentPart)
  , toolCallId :: Maybe String
  , toolCalls :: Maybe (Array CommonToolCall)
  , name :: Maybe String
  }

-- | Common usage
type CommonUsage =
  { inputTokens :: Maybe Int
  , outputTokens :: Maybe Int
  , totalTokens :: Maybe Int
  , promptTokens :: Maybe Int
  , completionTokens :: Maybe Int
  , cacheReadInputTokens :: Maybe Int
  , cacheCreationInputTokens :: Maybe Int
  , reasoningTokens :: Maybe Int
  }

-- | Tool choice type
data ToolChoice
  = ToolChoiceAuto
  | ToolChoiceNone
  | ToolChoiceRequired
  | ToolChoiceFunction String

derive instance eqToolChoice :: Eq ToolChoice

-- | Common request
type CommonRequest =
  { model :: String
  , maxTokens :: Maybe Int
  , temperature :: Maybe Number
  , topP :: Maybe Number
  , topK :: Maybe Int
  , stop :: Maybe (Array String)
  , messages :: Array CommonMessage
  , stream :: Maybe Boolean
  , tools :: Maybe (Array CommonTool)
  , toolChoice :: Maybe ToolChoice
  , systemPrompt :: Maybe String
  }

-- | Response choice
type ResponseChoice =
  { index :: Int
  , message :: ChoiceMessage
  , finishReason :: Maybe FinishReason
  }

type ChoiceMessage =
  { role :: MessageRole
  , content :: Maybe String
  , toolCalls :: Maybe (Array CommonToolCall)
  }

-- | Common response
type CommonResponse =
  { id :: String
  , object :: String
  , created :: Int
  , model :: String
  , choices :: Array ResponseChoice
  , usage :: Maybe CommonUsage
  }

-- | Chunk delta
type ChunkDelta =
  { role :: Maybe MessageRole
  , content :: Maybe String
  , toolCalls :: Maybe (Array ChunkToolCall)
  }

type ChunkToolCall =
  { index :: Int
  , id :: Maybe String
  , toolType :: Maybe String
  , functionName :: Maybe String
  , functionArguments :: Maybe String
  }

-- | Chunk choice
type ChunkChoice =
  { index :: Int
  , delta :: ChunkDelta
  , finishReason :: Maybe FinishReason
  }

-- | Common chunk
type CommonChunk =
  { id :: String
  , object :: String
  , created :: Int
  , model :: String
  , choices :: Array ChunkChoice
  , usage :: Maybe CommonUsage
  }

-- | Transform result
type TransformResult a = Either String a

-- ============================================================================
-- TRANSFORM FUNCTIONS
-- ============================================================================

-- | Transform request to target provider format
transformRequest :: ProviderFormat -> CommonRequest -> TransformResult Json
transformRequest format request = 
  transformRequestFFI (show format) request

foreign import transformRequestFFI :: String -> CommonRequest -> Either String Json

-- | Transform response from provider format to common format
transformResponse :: ProviderFormat -> Json -> TransformResult CommonResponse
transformResponse format json =
  transformResponseFFI (show format) json

foreign import transformResponseFFI :: String -> Json -> Either String CommonResponse

-- | Transform streaming chunk from provider format
transformChunk :: ProviderFormat -> Json -> TransformResult CommonChunk
transformChunk format json =
  transformChunkFFI (show format) json

foreign import transformChunkFFI :: String -> Json -> Either String CommonChunk

-- | Normalize usage from provider-specific format
normalizeUsage :: CommonUsage -> NormalizedUsage
normalizeUsage usage =
  { inputTokens: resolveTokens usage.inputTokens usage.promptTokens
  , outputTokens: resolveTokens usage.outputTokens usage.completionTokens
  , reasoningTokens: usage.reasoningTokens
  , cacheReadTokens: usage.cacheReadInputTokens
  , cacheWriteTokens: usage.cacheCreationInputTokens
  , totalTokens: usage.totalTokens
  }
  where
    resolveTokens primary secondary = case primary of
      Just p -> p
      Nothing -> case secondary of
        Just s -> s
        Nothing -> 0

type NormalizedUsage =
  { inputTokens :: Int
  , outputTokens :: Int
  , reasoningTokens :: Maybe Int
  , cacheReadTokens :: Maybe Int
  , cacheWriteTokens :: Maybe Int
  , totalTokens :: Maybe Int
  }
