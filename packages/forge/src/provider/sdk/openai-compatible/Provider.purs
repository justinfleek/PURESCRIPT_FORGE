-- | OpenAI Compatible Provider
module Forge.Provider.SDK.OpenAICompatible.Provider where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe(..))

-- | Provider configuration
type OpenAICompatibleProviderConfig =
  { baseUrl :: String
  , apiKey :: Maybe String
  , organizationId :: Maybe String
  , defaultModel :: Maybe String
  }

-- | Provider instance
type OpenAICompatibleProvider =
  { config :: OpenAICompatibleProviderConfig
  , name :: String
  }

-- | Create a new OpenAI compatible provider
create :: OpenAICompatibleProviderConfig -> OpenAICompatibleProvider
create config = { config, name: "openai-compatible" }

foreign import completeFFI :: String -> String -> String -> String -> Aff (Either String String)

-- | Generate a completion
complete :: OpenAICompatibleProvider -> String -> Aff (Either String String)
complete provider prompt = do
  let apiKey = case provider.config.apiKey of
        Just k -> k
        Nothing -> ""
  let model = case provider.config.defaultModel of
        Just m -> m
        Nothing -> "gpt-4"
  completeFFI provider.config.baseUrl apiKey model prompt
