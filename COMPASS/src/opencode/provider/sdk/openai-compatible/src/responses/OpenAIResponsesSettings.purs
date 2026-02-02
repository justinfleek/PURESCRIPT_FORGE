-- | OpenAI Responses Settings
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/provider/sdk/openai-compatible/src/responses/openai-responses-settings.ts
module Opencode.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesSettings where

import Prelude
import Data.Maybe (Maybe)

-- | Response settings
type ResponseSettings =
  { temperature :: Maybe Number
  , topP :: Maybe Number
  , maxTokens :: Maybe Int
  , frequencyPenalty :: Maybe Number
  , presencePenalty :: Maybe Number
  , stop :: Maybe (Array String)
  }

-- | Default response settings
defaultSettings :: ResponseSettings
defaultSettings =
  { temperature: Nothing
  , topP: Nothing
  , maxTokens: Nothing
  , frequencyPenalty: Nothing
  , presencePenalty: Nothing
  , stop: Nothing
  }
