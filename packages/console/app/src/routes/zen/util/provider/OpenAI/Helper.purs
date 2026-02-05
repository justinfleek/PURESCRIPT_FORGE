-- | OpenAI Provider Helper
-- | Core provider helper functions for OpenAI
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Provider.OpenAI.Helper
  ( openaiHelper
  , ProviderHelperInput
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Console.App.Routes.Omega.Util.Provider.Provider (UsageInfo)
import Console.App.Routes.Omega.Util.Provider.OpenAI.Usage (createUsageParser, normalizeUsage)

-- | Provider helper input
type ProviderHelperInput =
  { reqModel :: String
  , providerModel :: String
  }

-- | OpenAI provider helper
openaiHelper :: ProviderHelperInput -> ProviderHelper
openaiHelper _ =
  { format: "openai"
  , modifyUrl: \providerApi _isStream -> providerApi <> "/responses"
  , modifyHeaders: modifyHeadersImpl
  , modifyBody: identity
  , createBinaryStreamDecoder: \_ -> Nothing
  , streamSeparator: "\n\n"
  , createUsageParser
  , normalizeUsage
  }

-- | Modify headers (FFI boundary - Headers manipulation)
-- | Headers object is accessed via globalThis._currentHeadersObj (set by modifyHeadersFFI)
foreign import modifyHeadersImpl :: String -> String -> Unit
-- modifyHeadersImpl :: (Body, ApiKey) -> Unit
-- Mutates Headers object stored in globalThis._currentHeadersObj

-- | Provider helper type (matches ProviderHelper from provider.ts)
type ProviderHelper =
  { format :: String
  , modifyUrl :: String -> Maybe Boolean -> String
  , modifyHeaders :: String -> String -> Unit  -- body, apiKey (headers accessed via global)
  , modifyBody :: String -> String  -- JSON string in/out
  , createBinaryStreamDecoder :: Unit -> Maybe (String -> Maybe String)  -- Uint8Array -> Uint8Array | undefined
  , streamSeparator :: String
  , createUsageParser :: Unit -> UsageParser
  , normalizeUsage :: String -> UsageInfo  -- JSON usage -> UsageInfo
  }

-- | Usage parser type
type UsageParser =
  { parse :: String -> Unit
  , retrieve :: Unit -> Maybe String  -- Returns JSON string of usage
  }
