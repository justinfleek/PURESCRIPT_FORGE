-- | OpenAI Compatible Provider
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/provider/sdk/openai-compatible/src/openai-compatible-provider.ts
module Opencode.Provider.SDK.OpenAICompatible.Provider where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

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
