-- | OpenAI Configuration
module Forge.Provider.SDK.OpenAICompatible.Responses.OpenAIConfig where

import Prelude
import Data.Maybe (Maybe(..))

-- | OpenAI API configuration
type OpenAIConfig =
  { apiKey :: String
  , baseUrl :: Maybe String
  , organization :: Maybe String
  , timeout :: Maybe Int
  , maxRetries :: Maybe Int
  }

-- | Default configuration
defaultConfig :: String -> OpenAIConfig
defaultConfig apiKey =
  { apiKey
  , baseUrl: Nothing
  , organization: Nothing
  , timeout: Nothing
  , maxRetries: Nothing
  }
