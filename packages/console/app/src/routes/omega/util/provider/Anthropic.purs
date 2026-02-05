-- | Anthropic Provider Helper
-- | Provider helper for Anthropic Claude (including Bedrock support)
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/anthropic.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Provider.Anthropic
  ( anthropicHelper
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String as String
import Console.App.Routes.Omega.Util.Provider.Provider (UsageInfo)
import Console.App.Routes.Omega.Util.Provider.Anthropic.Request (fromAnthropicRequest, toAnthropicRequest)
import Console.App.Routes.Omega.Util.Provider.Anthropic.Response (fromAnthropicResponse, toAnthropicResponse)
import Console.App.Routes.Omega.Util.Provider.Anthropic.Chunk (fromAnthropicChunk, toAnthropicChunk)

-- | Provider helper input
type ProviderHelperInput =
  { reqModel :: String
  , providerModel :: String
  }

-- | Anthropic provider helper
anthropicHelper :: ProviderHelperInput -> ProviderHelper
anthropicHelper { reqModel, providerModel } =
  let
    isBedrockModelArn = String.startsWith (String.Pattern "arn:aws:bedrock:") providerModel
    isBedrockModelID = String.startsWith (String.Pattern "global.anthropic.") providerModel
    isBedrock = isBedrockModelArn || isBedrockModelID
    isSonnet = String.contains (String.Pattern "sonnet") reqModel
  in
    { format: "anthropic"
    , modifyUrl: \providerApi isStream ->
        if isBedrock
          then providerApi <> "/model/" <>
               (if isBedrockModelArn then encodeURIComponent providerModel else providerModel) <> "/" <>
               (if isStream == Just true then "invoke-with-response-stream" else "invoke")
          else providerApi <> "/messages"
    , modifyHeaders: \bodyJson apiKey -> modifyHeadersImpl isBedrock isSonnet bodyJson apiKey
    , modifyBody: \bodyJson -> modifyBodyImpl isBedrock isSonnet bodyJson
    , createBinaryStreamDecoder: createBinaryStreamDecoderImpl isBedrock
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

-- | Modify headers (FFI boundary - mutates Headers object in globalThis._currentHeadersObj)
foreign import modifyHeadersImpl :: Boolean -> Boolean -> String -> String -> Unit

-- | Modify body (FFI boundary)
foreign import modifyBodyImpl :: Boolean -> Boolean -> String -> String

-- | Create binary stream decoder (FFI boundary)
foreign import createBinaryStreamDecoderImpl :: Boolean -> Unit -> Maybe (String -> Maybe String)

-- | Create usage parser (FFI boundary)
foreign import createUsageParserImpl :: Unit -> UsageParser

-- | Normalize usage (FFI boundary)
foreign import normalizeUsageImpl :: String -> UsageInfo

-- | Encode URI component (FFI boundary)
foreign import encodeURIComponent :: String -> String
