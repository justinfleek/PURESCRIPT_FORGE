-- | Google Provider Helper
-- | Provider helper for Google Gemini
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/google.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Provider.Google
  ( googleHelper
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Console.App.Routes.Omega.Util.Provider.Provider (UsageInfo)
import Console.App.Routes.Omega.Util.Provider.Google.Request (fromGoogleRequest, toGoogleRequest)
import Console.App.Routes.Omega.Util.Provider.Google.Response (fromGoogleResponse, toGoogleResponse)
import Console.App.Routes.Omega.Util.Provider.Google.Chunk (fromGoogleChunk, toGoogleChunk)

-- | Provider helper input
type ProviderHelperInput =
  { reqModel :: String
  , providerModel :: String
  }

-- | Google provider helper
googleHelper :: ProviderHelperInput -> ProviderHelper
googleHelper { providerModel } =
  { format: "google"
  , modifyUrl: \providerApi isStream ->
      providerApi <> "/models/" <> providerModel <> ":" <>
      (if isStream == Just true then "streamGenerateContent?alt=sse" else "generateContent")
  , modifyHeaders: modifyHeadersImpl
  , modifyBody: identity
  , createBinaryStreamDecoder: \_ -> Nothing
  , streamSeparator: "\r\n\r\n"
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

-- | Create usage parser (FFI boundary)
foreign import createUsageParserImpl :: Unit -> UsageParser

-- | Normalize usage (FFI boundary)
foreign import normalizeUsageImpl :: String -> UsageInfo
