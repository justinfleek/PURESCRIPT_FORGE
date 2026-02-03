-- | OpenAI Compatible Provider
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/provider/sdk/openai-compatible/src/openai-compatible-provider.ts
module Forge.Provider.SDK.OpenAICompatible.Provider where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

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

-- | Generate a completion
complete :: OpenAICompatibleProvider -> String -> Aff (Either String String)
complete provider prompt = notImplemented "Provider.SDK.OpenAICompatible.Provider.complete"
