-- | OpenAI Responses Language Model
-- | Ported from: openai-responses-language-model.ts
module Forge.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesLanguageModel where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Forge.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesAPITypes (ChatCompletionRequest, ChatCompletionResponse)

-- | Language model configuration
type LanguageModelConfig =
  { model :: String
  , baseUrl :: String
  , apiKey :: String
  }

-- | Create a chat completion via OpenAI-compatible API
createChatCompletion :: LanguageModelConfig -> ChatCompletionRequest -> Aff (Either String ChatCompletionResponse)
createChatCompletion config req = fromEffectFnAff (createChatCompletionFFI config req)

-- | Create a streaming chat completion
-- | Returns Either String Unit (streaming results come via callback)
createStreamingChatCompletion :: LanguageModelConfig -> ChatCompletionRequest -> Aff (Either String Unit)
createStreamingChatCompletion config req =
  fromEffectFnAff (createStreamingChatCompletionFFI config req)

-- | FFI: Non-streaming chat completion
foreign import createChatCompletionFFI :: LanguageModelConfig -> ChatCompletionRequest -> EffectFnAff (Either String ChatCompletionResponse)

-- | FFI: Streaming chat completion
foreign import createStreamingChatCompletionFFI :: LanguageModelConfig -> ChatCompletionRequest -> EffectFnAff (Either String Unit)
