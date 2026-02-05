-- | OpenAI-Compatible Provider Helper
-- | Provider helper for OpenAI-compatible APIs
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai-compatible.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Provider.OpenAICompatible
  ( oaCompatHelper
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Console.App.Routes.Omega.Util.Provider.Provider (UsageInfo)
import Console.App.Routes.Omega.Util.Provider.OpenAICompatible.Request (fromOaCompatibleRequest, toOaCompatibleRequest)
import Console.App.Routes.Omega.Util.Provider.OpenAICompatible.Response (fromOaCompatibleResponse, toOaCompatibleResponse)
import Console.App.Routes.Omega.Util.Provider.OpenAICompatible.Chunk (fromOaCompatibleChunk, toOaCompatibleChunk)

-- | Provider helper input
type ProviderHelperInput =
  { reqModel :: String
  , providerModel :: String
  }

-- | OpenAI-compatible provider helper
oaCompatHelper :: ProviderHelperInput -> ProviderHelper
oaCompatHelper _ =
  { format: "oa-compat"
  , modifyUrl: \providerApi _isStream -> providerApi <> "/chat/completions"
  , modifyHeaders: modifyHeadersImpl
  , modifyBody: modifyBodyImpl
  , createBinaryStreamDecoder: \_ -> Nothing
  , streamSeparator: "\n\n"
  , createUsageParser: createUsageParserImpl
  , normalizeUsage: normalizeUsageImpl
  }

-- | Provider helper type
type ProviderHelper =
  { format :: String
  , modifyUrl :: String -> Maybe Boolean -> String
  , modifyHeaders :: String -> String -> Unit  -- body, apiKey (headers accessed via global)
  , modifyBody :: String -> String
  , createBinaryStreamDecoder :: Unit -> Maybe (String -> Maybe String)
  , streamSeparator :: String
  , createUsageParser :: Unit -> UsageParser
  , normalizeUsage :: String -> UsageInfo
  }

-- | Usage parser type
type UsageParser =
  { parse :: String -> Unit
  , retrieve :: Unit -> Maybe String
  }

-- | Modify headers (FFI boundary)
foreign import modifyHeadersImpl :: String -> String -> String -> Unit

-- | Modify body (FFI boundary)
foreign import modifyBodyImpl :: String -> String

-- | Create usage parser (FFI boundary)
foreign import createUsageParserImpl :: Unit -> UsageParser

-- | Normalize usage (FFI boundary)
foreign import normalizeUsageImpl :: String -> UsageInfo
