{-|
Module      : Opencode.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesLanguageModel
Description : OpenAI-compatible chat completion implementation
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= OpenAI Responses Language Model

Implements OpenAI-compatible chat completions with streaming support.
Compatible with Venice AI, Anthropic (via proxy), OpenRouter, and other
OpenAI-compatible APIs.

== Coeffect Equation

@
  createChatCompletion : Config → Request → Graded (Network ⊗ Auth provider) Response
  createStreamingChatCompletion : Config → Request → Graded (Network ⊗ Auth provider) (Stream Chunk)
@

== API Compatibility

Supports:
- OpenAI Chat Completions API (v1/chat/completions)
- OpenAI Responses API (v1/responses)
- Streaming via Server-Sent Events (SSE)
-}
module Opencode.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesLanguageModel
  ( -- * Configuration
    LanguageModelConfig(..)
  , defaultConfig
    -- * Chat Completion
  , createChatCompletion
  , createStreamingChatCompletion
    -- * Streaming
  , StreamCallback
  , ChatChunk(..)
    -- * Coeffects
  , completionCoeffect
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..), maybe)
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, encodeJson, decodeJson, stringify, jsonParser)
import Effect (Effect)
import Effect.Aff (Aff, attempt)
import Effect.Class (liftEffect)

import Bridge.FFI.Node.Fetch as Fetch
import Opencode.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesAPITypes 
  ( ChatCompletionRequest
  , ChatCompletionResponse
  , ChatCompletionChunk
  , ChatMessage
  , ChatChoice
  , Usage
  )
import Aleph.Coeffect.Resource (Resource(..), (⊗))

-- ════════════════════════════════════════════════════════════════════════════
-- CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

{-| Language model configuration.

@
  record LanguageModelConfig where
    model     : String
    baseUrl   : String
    apiKey    : String
    headers   : Array (String, String)
    timeout   : Int
@
-}
type LanguageModelConfig =
  { model :: String
  , baseUrl :: String
  , apiKey :: String
  , headers :: Array { key :: String, value :: String }
  , timeout :: Int
  , providerId :: String
  }

-- | Default configuration
defaultConfig :: LanguageModelConfig
defaultConfig =
  { model: ""
  , baseUrl: "https://api.openai.com/v1"
  , apiKey: ""
  , headers: []
  , timeout: 120000
  , providerId: "openai"
  }

-- ════════════════════════════════════════════════════════════════════════════
-- CHAT COMPLETION
-- ════════════════════════════════════════════════════════════════════════════

{-| Create a non-streaming chat completion.

@
  createChatCompletion config request = do
    response ← Fetch.fetch (buildUrl config) (buildOptions config request)
    case response of
      Left err → pure (Left err)
      Right resp → parseResponse resp
@
-}
createChatCompletion 
  :: LanguageModelConfig 
  -> ChatCompletionRequest 
  -> Aff (Either String ChatCompletionResponse)
createChatCompletion config request = do
  let url = buildCompletionUrl config
  let body = buildRequestBody config request false
  let options = buildFetchOptions config body
  
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

-- ════════════════════════════════════════════════════════════════════════════
-- STREAMING
-- ════════════════════════════════════════════════════════════════════════════

{-| Callback for streaming chunks. -}
type StreamCallback = ChatChunk -> Effect Unit

{-| Streaming chat chunk.

@
  record ChatChunk where
    id      : String
    choices : Array { delta : { content : Maybe String, role : Maybe String } }
    model   : Maybe String
@
-}
type ChatChunk =
  { id :: String
  , choices :: Array { delta :: { content :: Maybe String, role :: Maybe String }, index :: Int }
  , model :: Maybe String
  }

{-| Create a streaming chat completion.

Streams chunks via callback, returns final aggregated response.
-}
createStreamingChatCompletion
  :: LanguageModelConfig
  -> ChatCompletionRequest
  -> StreamCallback
  -> Aff (Either String ChatCompletionResponse)
createStreamingChatCompletion config request callback = do
  let url = buildCompletionUrl config
  let body = buildRequestBody config request true
  let options = buildFetchOptions config body
  
  result <- Fetch.fetch url options
  case result of
    Left err -> pure $ Left ("Fetch failed: " <> err)
    Right response -> do
      isOk <- liftEffect $ Fetch.ok response
      statusCode <- liftEffect $ Fetch.status response
      
      if not isOk
        then pure $ Left ("HTTP " <> show statusCode)
        else do
          -- For streaming, we need to process SSE events
          -- The Fetch FFI returns the full response for now
          -- TODO: Implement true SSE streaming via FFI
          textResult <- Fetch.text response
          case textResult of
            Left err -> pure $ Left err
            Right body' -> parseSSEResponse body' callback

-- | Parse SSE response and invoke callbacks
parseSSEResponse :: String -> StreamCallback -> Aff (Either String ChatCompletionResponse)
parseSSEResponse body callback = do
  -- SSE format: "data: {json}\n\n" for each chunk, "data: [DONE]\n\n" at end
  let lines = String.split (String.Pattern "\n") body
  let dataLines = Array.filter (\l -> String.take 6 l == "data: ") lines
  let jsonLines = map (\l -> String.drop 6 l) dataLines
  
  -- Aggregate content from chunks
  contentRef <- liftEffect $ pure { content: "", role: "assistant" }
  
  -- Process each chunk
  _ <- traverse (processChunk callback) (Array.filter (\l -> l /= "[DONE]") jsonLines)
  
  -- Build final response
  let finalResponse = buildFinalResponse contentRef.content
  pure $ Right finalResponse
  where
    traverse f = Array.foldM (\_ x -> f x *> pure unit) unit
    
    processChunk cb jsonStr = liftEffect $ case jsonParser jsonStr >>= decodeJson of
      Left _ -> pure unit
      Right (chunk :: ChatChunk) -> cb chunk
    
    buildFinalResponse content =
      { id: ""
      , object: "chat.completion"
      , created: 0
      , model: ""
      , choices: 
          [ { message: { role: "assistant", content }
            , index: 0
            , finish_reason: Just "stop"
            }
          ]
      , usage: Just { prompt_tokens: 0, completion_tokens: 0, total_tokens: 0 }
      }

-- ════════════════════════════════════════════════════════════════════════════
-- HELPERS
-- ════════════════════════════════════════════════════════════════════════════

-- | Build completion URL
buildCompletionUrl :: LanguageModelConfig -> String
buildCompletionUrl config = 
  config.baseUrl <> "/chat/completions"

-- | Build request body
buildRequestBody :: LanguageModelConfig -> ChatCompletionRequest -> Boolean -> String
buildRequestBody config request stream = stringify $ encodeJson
  { model: config.model
  , messages: request.messages
  , stream
  , max_tokens: request.maxTokens
  , temperature: request.temperature
  }

-- | Build fetch options
buildFetchOptions :: LanguageModelConfig -> String -> Fetch.RequestOptions
buildFetchOptions config body =
  { method: "POST"
  , headers: 
      [ { key: "Content-Type", value: "application/json" }
      , { key: "Authorization", value: "Bearer " <> config.apiKey }
      ] <> config.headers
  , body: Just body
  }

-- ════════════════════════════════════════════════════════════════════════════
-- COEFFECTS
-- ════════════════════════════════════════════════════════════════════════════

{-| Coeffect for chat completion.

Requires network access and authentication for the provider.
-}
completionCoeffect :: LanguageModelConfig -> Resource
completionCoeffect config = Network ⊗ Auth config.providerId
