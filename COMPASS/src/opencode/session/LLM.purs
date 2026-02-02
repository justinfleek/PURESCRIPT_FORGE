{-|
Module      : Opencode.Session.LLM
Description : LLM API client for chat completions
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= LLM Client

Handles communication with language model providers via OpenAI-compatible API.
Types are imported from LLMTypes module.

== Coeffect Equation

@
  complete : ProviderConfig × LLMRequest -> Graded HTTP (Either Error LLMResponse)
  stream   : ProviderConfig × LLMRequest × Handler -> Graded HTTP (Either Error Canceler)
@

== Protocol

- All requests/responses follow JSON-RPC 2.0 format
- Tool calls follow OpenAI function calling schema
- Streaming uses Server-Sent Events (SSE)

-}
module Opencode.Session.LLM
  ( -- * Re-exports from LLMTypes
    module Opencode.Session.LLMTypes
    -- * API Functions
  , complete
  , stream
    -- * Message Builders
  , userMessage
  , systemMessage
  , assistantMessage
  , toolResultMessage
    -- * Response Helpers
  , hasToolCalls
  , getToolCalls
  , totalTokens
    -- * Conversion Utilities
  , contentToString
  , toAPIMessage
  , fromAPIResponse
  ) where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.Argonaut (encodeJson, decodeJson, stringify, jsonParser)
import Data.String as String

-- Import Bridge FFI for HTTP calls
import Bridge.FFI.Node.Fetch as Fetch

-- Import types from LLMTypes
import Opencode.Session.LLMTypes

-- ════════════════════════════════════════════════════════════════════════════
-- MESSAGE BUILDERS
-- ════════════════════════════════════════════════════════════════════════════

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

-- | Create an assistant message
assistantMessage :: String -> LLMMessage
assistantMessage content =
  { role: Assistant
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

-- ════════════════════════════════════════════════════════════════════════════
-- RESPONSE HELPERS
-- ════════════════════════════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════════════════════════════
-- API CALLS
-- ════════════════════════════════════════════════════════════════════════════

-- | Send a non-streaming request to the LLM
complete :: ProviderConfig -> LLMRequest -> Aff (Either String LLMResponse)
complete config request = do
  let chatRequest = buildChatRequest request
  result <- callChatCompletion config chatRequest
  case result of
    Left err -> pure $ Left err
    Right resp -> pure $ Right (fromAPIResponse resp)

-- | Stream a completion from the LLM
stream :: ProviderConfig -> LLMRequest -> StreamHandler -> Aff (Either String (Aff Unit))
stream config request handler = do
  let chatRequest = buildChatRequest request
  callStreamingCompletion config chatRequest handler

-- | Build API chat request from LLMRequest
buildChatRequest :: LLMRequest -> APIChatRequest
buildChatRequest request =
  { model: request.model
  , messages: map toAPIMessage request.messages
  , temperature: request.temperature
  , maxTokens: request.maxTokens
  , topP: Nothing
  , frequencyPenalty: Nothing
  , presencePenalty: Nothing
  , stop: Nothing
  , stream: Just request.stream
  , tools: map toAPITools request.tools
  , toolChoice: map toAPIToolChoice request.toolChoice
  }

-- ════════════════════════════════════════════════════════════════════════════
-- TYPE CONVERSIONS
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert ContentPart array to string
contentToString :: Array ContentPart -> String
contentToString parts = case Array.head parts of
  Nothing -> ""
  Just (TextPart s) -> s
  Just (ImagePart _) -> "[image]"
  Just (ToolResultPart r) -> r.content

-- | Convert LLMMessage to API format
toAPIMessage :: LLMMessage -> APIMessage
toAPIMessage msg =
  { role: showRole msg.role
  , content: contentToString msg.content
  , name: msg.name
  , tool_calls: map (map toAPIToolCall) msg.toolCalls
  , tool_call_id: msg.toolCallId
  }

-- | Convert ToolCall to API format
toAPIToolCall :: ToolCall -> APIToolCall
toAPIToolCall tc =
  { id: tc.id
  , "type": tc."type"
  , function: { name: tc.function.name, arguments: tc.function.arguments }
  }

-- | Convert tool definitions to API format
toAPITools :: Array ToolDefinition -> Array APIToolDefinition
toAPITools = map \td ->
  { "type": td."type"
  , function: 
      { name: td.function.name
      , description: Just td.function.description
      , parameters: td.function.parameters
      }
  }

-- | Convert ToolChoice to API string
toAPIToolChoice :: ToolChoice -> String
toAPIToolChoice = case _ of
  Auto -> "auto"
  None -> "none"
  Required -> "required"
  Specific name -> name

-- | Convert API response to LLMResponse
fromAPIResponse :: APIResponse -> LLMResponse
fromAPIResponse resp =
  { id: resp.id
  , model: resp.model
  , choices: map fromAPIChoice resp.choices
  , usage: fromMaybe defaultUsage (map fromAPIUsage resp.usage)
  }

-- | Convert API choice to Choice
fromAPIChoice :: APIChoice -> Choice
fromAPIChoice choice =
  { index: choice.index
  , message: fromAPIMessage choice.message
  , finishReason: parseFinishReason (fromMaybe "stop" choice.finish_reason)
  }

-- | Convert API message to LLMMessage
fromAPIMessage :: APIMessage -> LLMMessage
fromAPIMessage msg =
  { role: parseRole msg.role
  , content: [TextPart msg.content]
  , name: msg.name
  , toolCalls: map (map fromAPIToolCall) msg.tool_calls
  , toolCallId: msg.tool_call_id
  }

-- | Convert API tool call to ToolCall
fromAPIToolCall :: APIToolCall -> ToolCall
fromAPIToolCall tc =
  { id: tc.id
  , "type": tc."type"
  , function: { name: tc.function.name, arguments: tc.function.arguments }
  }

-- | Convert API usage to LLMUsage
fromAPIUsage :: APIUsage -> LLMUsage
fromAPIUsage u =
  { promptTokens: u.prompt_tokens
  , completionTokens: u.completion_tokens
  , totalTokens: u.total_tokens
  , cacheHit: Nothing
  , cacheWrite: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
-- HTTP IMPLEMENTATION
-- ════════════════════════════════════════════════════════════════════════════

-- | Call chat completion API
callChatCompletion :: ProviderConfig -> APIChatRequest -> Aff (Either String APIResponse)
callChatCompletion config request = do
  let url = config.baseUrl <> "/chat/completions"
  let body = stringify $ encodeJson
        { model: request.model
        , messages: request.messages
        , stream: request.stream
        , max_tokens: request.maxTokens
        , temperature: request.temperature
        , tools: request.tools
        , tool_choice: request.toolChoice
        }
  let options =
        { method: "POST"
        , headers:
            [ { key: "Content-Type", value: "application/json" }
            , { key: "Authorization", value: "Bearer " <> config.apiKey }
            ] <> config.headers
        , body: Just body
        }
  
  result <- Fetch.fetch url options
  case result of
    Left err -> pure $ Left ("Fetch failed: " <> err)
    Right response -> do
      isOk <- liftEffect $ Fetch.ok response
      statusCode <- liftEffect $ Fetch.status response
      
      if not isOk
        then do
          textResult <- Fetch.text response
          case textResult of
            Left _ -> pure $ Left ("HTTP " <> show statusCode)
            Right body' -> pure $ Left ("HTTP " <> show statusCode <> ": " <> body')
        else do
          textResult <- Fetch.text response
          case textResult of
            Left err -> pure $ Left ("Failed to read response: " <> err)
            Right body' -> case jsonParser body' >>= decodeJson of
              Left err -> pure $ Left ("JSON parse error: " <> show err)
              Right resp -> pure $ Right resp

-- | Call streaming chat completion API
callStreamingCompletion 
  :: ProviderConfig 
  -> APIChatRequest 
  -> StreamHandler 
  -> Aff (Either String (Aff Unit))
callStreamingCompletion config request handler = do
  let url = config.baseUrl <> "/chat/completions"
  let body = stringify $ encodeJson
        { model: request.model
        , messages: request.messages
        , stream: Just true
        , max_tokens: request.maxTokens
        , temperature: request.temperature
        , tools: request.tools
        , tool_choice: request.toolChoice
        }
  let options =
        { method: "POST"
        , headers:
            [ { key: "Content-Type", value: "application/json" }
            , { key: "Authorization", value: "Bearer " <> config.apiKey }
            ] <> config.headers
        , body: Just body
        }
  
  result <- Fetch.fetch url options
  case result of
    Left err -> pure $ Left ("Fetch failed: " <> err)
    Right response -> do
      isOk <- liftEffect $ Fetch.ok response
      statusCode <- liftEffect $ Fetch.status response
      
      if not isOk
        then pure $ Left ("HTTP " <> show statusCode)
        else do
          textResult <- Fetch.text response
          case textResult of
            Left err -> pure $ Left err
            Right body' -> do
              parseSSEAndCallback body' handler
              pure $ Right (pure unit)

-- | Parse SSE response and invoke handler callbacks
parseSSEAndCallback :: String -> StreamHandler -> Aff Unit
parseSSEAndCallback body handler = do
  let lines = String.split (String.Pattern "\n") body
  let dataLines = Array.filter (\l -> String.take 6 l == "data: ") lines
  let jsonLines = map (\l -> String.drop 6 l) dataLines
  
  _ <- traverseAff processChunk (Array.filter (\l -> l /= "[DONE]") jsonLines)
  handler.onDone defaultUsage
  pure unit
  where
    processChunk :: String -> Aff Unit
    processChunk jsonStr = case jsonParser jsonStr >>= decodeJson of
      Left _ -> pure unit
      Right (chunk :: APIStreamChunk) -> handler.onChunk (fromAPIStreamChunk chunk)

-- | Convert API stream chunk to StreamChunk
fromAPIStreamChunk :: APIStreamChunk -> StreamChunk
fromAPIStreamChunk chunk =
  case Array.head chunk.choices of
    Nothing -> 
      { id: chunk.id
      , model: chunk.model
      , delta: { role: Nothing, content: Nothing, toolCalls: Nothing }
      , finishReason: Nothing
      }
    Just choice ->
      { id: chunk.id
      , model: chunk.model
      , delta: 
          { role: map parseRole choice.delta.role
          , content: choice.delta.content
          , toolCalls: map (map fromAPIToolCall) choice.delta.tool_calls
          }
      , finishReason: map parseFinishReason choice.finish_reason
      }

-- ════════════════════════════════════════════════════════════════════════════
-- HELPERS
-- ════════════════════════════════════════════════════════════════════════════

fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe def = case _ of
  Nothing -> def
  Just a -> a

-- | Traverse array in Aff
traverseAff :: forall a b. (a -> Aff b) -> Array a -> Aff (Array b)
traverseAff f arr = case Array.uncons arr of
  Nothing -> pure []
  Just { head, tail } -> do
    b <- f head
    bs <- traverseAff f tail
    pure $ Array.cons b bs
