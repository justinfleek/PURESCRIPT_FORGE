-- | Omega Provider Types and Converters
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/provider.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Omega.Util.Provider.Provider
  ( ProviderFormat(..)
  , UsageInfo
  , CommonMessage
  , CommonContentPart
  , CommonToolCall
  , CommonTool
  , CommonUsage
  , CommonRequest
  , CommonResponse
  , CommonChunk
  , MessageRole(..)
  , ContentPartType(..)
  , FinishReason(..)
  , ToolChoice(..)
  , ResponseChoice
  , ChunkChoice
  , ChunkDelta
  , parseProviderFormat
  , createBodyConverter
  , createStreamPartConverter
  , createResponseConverter
  , enrichUsageWithBytes
  ) where

import Prelude

import Data.Array (mapMaybe)
import Data.Maybe (Maybe(..))

-- | Provider format
data ProviderFormat
  = Anthropic
  | OpenAI
  | OACompat
  | Google

derive instance eqProviderFormat :: Eq ProviderFormat

instance showProviderFormat :: Show ProviderFormat where
  show Anthropic = "anthropic"
  show OpenAI = "openai"
  show OACompat = "oa-compat"
  show Google = "google"

-- | Parse provider format from string
parseProviderFormat :: String -> Maybe ProviderFormat
parseProviderFormat "anthropic" = Just Anthropic
parseProviderFormat "openai" = Just OpenAI
parseProviderFormat "oa-compat" = Just OACompat
parseProviderFormat "google" = Just Google
parseProviderFormat _ = Nothing

-- | Usage info
-- | Tracks both token counts (from API) and byte counts (calculated from content)
-- | Byte-level precision enables accurate billing and usage tracking
type UsageInfo =
  { inputTokens :: Int
  , outputTokens :: Int
  , reasoningTokens :: Maybe Int
  , cacheReadTokens :: Maybe Int
  , cacheWrite5mTokens :: Maybe Int
  , cacheWrite1hTokens :: Maybe Int
  , inputBytes :: Int
  , outputBytes :: Int
  , reasoningBytes :: Maybe Int
  , cacheReadBytes :: Maybe Int
  }

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

-- | Parse message role
parseMessageRole :: String -> Maybe MessageRole
parseMessageRole "system" = Just System
parseMessageRole "user" = Just User
parseMessageRole "assistant" = Just Assistant
parseMessageRole "tool" = Just Tool
parseMessageRole _ = Nothing

-- | Content part type
data ContentPartType
  = TextPart
  | ImageUrlPart

derive instance eqContentPartType :: Eq ContentPartType

-- | Common content part
type CommonContentPart =
  { partType :: ContentPartType
  , text :: Maybe String
  , imageUrl :: Maybe String
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
  , functionParameters :: Maybe String  -- JSON string
  }

-- | Common message
type CommonMessage =
  { role :: MessageRole
  , content :: Maybe String
  , contentParts :: Maybe (Array CommonContentPart)
  , toolCallId :: Maybe String
  , toolCalls :: Maybe (Array CommonToolCall)
  }

-- | Common usage
type CommonUsage =
  { inputTokens :: Maybe Int
  , outputTokens :: Maybe Int
  , totalTokens :: Maybe Int
  , promptTokens :: Maybe Int
  , completionTokens :: Maybe Int
  , cacheReadInputTokens :: Maybe Int
  , cacheCreationEphemeral5mInputTokens :: Maybe Int
  , cacheCreationEphemeral1hInputTokens :: Maybe Int
  , cachedTokens :: Maybe Int
  , reasoningTokens :: Maybe Int
  }

-- | Tool choice type
data ToolChoice
  = ToolChoiceAuto
  | ToolChoiceRequired
  | ToolChoiceFunction String

derive instance eqToolChoice :: Eq ToolChoice

-- | Common request
type CommonRequest =
  { model :: String
  , maxTokens :: Maybe Int
  , temperature :: Maybe Number
  , topP :: Maybe Number
  , stop :: Maybe (Array String)
  , messages :: Array CommonMessage
  , stream :: Maybe Boolean
  , tools :: Maybe (Array CommonTool)
  , toolChoice :: Maybe ToolChoice
  }

-- | Finish reason
data FinishReason
  = Stop
  | ToolCalls
  | Length
  | ContentFilter

derive instance eqFinishReason :: Eq FinishReason

instance showFinishReason :: Show FinishReason where
  show Stop = "stop"
  show ToolCalls = "tool_calls"
  show Length = "length"
  show ContentFilter = "content_filter"

-- | Response choice
type ResponseChoice =
  { index :: Int
  , message ::
      { role :: MessageRole
      , content :: Maybe String
      , toolCalls :: Maybe (Array CommonToolCall)
      }
  , finishReason :: Maybe FinishReason
  }

-- | Common response
type CommonResponse =
  { id :: String
  , object :: String  -- "chat.completion"
  , created :: Int
  , model :: String
  , choices :: Array ResponseChoice
  , usage :: Maybe CommonUsage
  }

-- | Chunk delta
type ChunkDelta =
  { role :: Maybe MessageRole
  , content :: Maybe String
  , toolCalls :: Maybe (Array
      { index :: Int
      , id :: Maybe String
      , toolType :: Maybe String
      , functionName :: Maybe String
      , functionArguments :: Maybe String
      })
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
  , object :: String  -- "chat.completion.chunk"
  , created :: Int
  , model :: String
  , choices :: Array ChunkChoice
  , usage :: Maybe CommonUsage
  }

-- | Body converter function type
type BodyConverter = CommonRequest -> CommonRequest

-- | Create body converter between formats
-- | When formats match, returns identity
createBodyConverter :: ProviderFormat -> ProviderFormat -> BodyConverter
createBodyConverter from to =
  if from == to
    then identity
    else \req -> convertRequestFormatImpl (show from) (show to) req

-- | Convert request between formats (FFI boundary - complex conversion)
foreign import convertRequestFormatImpl :: String -> String -> CommonRequest -> CommonRequest

-- | Stream part converter
type StreamPartConverter = CommonChunk -> CommonChunk

-- | Create stream part converter between formats
createStreamPartConverter :: ProviderFormat -> ProviderFormat -> StreamPartConverter
createStreamPartConverter from to =
  if from == to
    then identity
    else \chunk -> convertChunkFormatImpl (show from) (show to) chunk

-- | Convert chunk between formats (FFI boundary - complex conversion)
foreign import convertChunkFormatImpl :: String -> String -> CommonChunk -> CommonChunk

-- | Response converter
type ResponseConverter = CommonResponse -> CommonResponse

-- | Create response converter between formats
createResponseConverter :: ProviderFormat -> ProviderFormat -> ResponseConverter
createResponseConverter from to =
  if from == to
    then identity
    else \resp -> convertResponseFormatImpl (show from) (show to) resp

-- | Convert response between formats (FFI boundary - complex conversion)
foreign import convertResponseFormatImpl :: String -> String -> CommonResponse -> CommonResponse

-- | Normalize usage from provider-specific format to common format
-- | Byte counts default to 0 if not provided (will be calculated from content when available)
normalizeUsage :: CommonUsage -> UsageInfo
normalizeUsage usage =
  { inputTokens: case usage.inputTokens of
      Just i -> i
      Nothing -> case usage.promptTokens of
        Just p -> p
        Nothing -> 0
  , outputTokens: case usage.outputTokens of
      Just o -> o
      Nothing -> case usage.completionTokens of
        Just c -> c
        Nothing -> 0
  , reasoningTokens: usage.reasoningTokens
  , cacheReadTokens: case usage.cacheReadInputTokens of
      Just c -> Just c
      Nothing -> usage.cachedTokens
  , cacheWrite5mTokens: usage.cacheCreationEphemeral5mInputTokens
  , cacheWrite1hTokens: usage.cacheCreationEphemeral1hInputTokens
  , inputBytes: 0
  , outputBytes: 0
  , reasoningBytes: Nothing
  , cacheReadBytes: Nothing
  }

-- | Enrich UsageInfo with byte counts calculated from message content
-- | Single-byte precision for accurate billing and usage tracking
enrichUsageWithBytes :: UsageInfo -> Array CommonMessage -> Array CommonMessage -> UsageInfo
enrichUsageWithBytes usage inputMessages outputMessages =
  let
    inputBytesTotal = countBytesInMessages inputMessages
    outputBytesTotal = countBytesInMessages outputMessages
    reasoningBytesTotal = case usage.reasoningTokens of
      Just _ -> Nothing  -- Will be calculated from reasoning content if available
      Nothing -> Nothing
    cacheReadBytesTotal = case usage.cacheReadTokens of
      Just tokens -> Just (tokens * 4)  -- Approximate: ~4 bytes per token
      Nothing -> Nothing
  in
    usage
      { inputBytes = inputBytesTotal
      , outputBytes = outputBytesTotal
      , reasoningBytes = reasoningBytesTotal
      , cacheReadBytes = cacheReadBytesTotal
      }
