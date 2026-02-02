-- | OpenAI Responses Language Model
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/provider/sdk/openai-compatible/src/responses/openai-responses-language-model.ts
module Opencode.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesLanguageModel where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesAPITypes (ChatCompletionRequest, ChatCompletionResponse)
import Opencode.Util.NotImplemented (notImplemented)

-- | Language model configuration
type LanguageModelConfig =
  { model :: String
  , baseUrl :: String
  , apiKey :: String
  }

-- | Create a chat completion
createChatCompletion :: LanguageModelConfig -> ChatCompletionRequest -> Aff (Either String ChatCompletionResponse)
createChatCompletion config request = notImplemented "Responses.OpenAIResponsesLanguageModel.createChatCompletion"

-- | Create a streaming chat completion
createStreamingChatCompletion :: LanguageModelConfig -> ChatCompletionRequest -> Aff (Either String Unit)
createStreamingChatCompletion config request = notImplemented "Responses.OpenAIResponsesLanguageModel.createStreamingChatCompletion"
