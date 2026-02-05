-- | OpenAI Usage Parser and Normalizer
-- | Parses usage from OpenAI response format
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Provider.OpenAI.Usage
  ( createUsageParser
  , normalizeUsage
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String as String
import Console.App.Routes.Omega.Util.Provider.Provider (UsageInfo)

-- | Usage parser type
type UsageParser =
  { parse :: String -> Unit
  , retrieve :: Unit -> Maybe String  -- Returns JSON string of usage
  }

-- | Create usage parser
createUsageParser :: Unit -> UsageParser
createUsageParser _ =
  { parse: parseUsageImpl
  , retrieve: retrieveUsageImpl
  }

-- | Parse usage from chunk (FFI boundary - JSON parsing)
foreign import parseUsageImpl :: String -> Unit

-- | Retrieve parsed usage (FFI boundary - returns JSON string)
foreign import retrieveUsageImpl :: Unit -> Maybe String

-- | Normalize usage from OpenAI format to common format
normalizeUsage :: String -> UsageInfo
normalizeUsage usageJson = do
  let usage = parseUsageJson usageJson
  { inputTokens: (usage.inputTokens # fromMaybe 0) - (usage.cacheReadTokens # fromMaybe 0)
  , outputTokens: (usage.outputTokens # fromMaybe 0) - (usage.reasoningTokens # fromMaybe 0)
  , reasoningTokens: usage.reasoningTokens
  , cacheReadTokens: usage.cacheReadTokens
  , cacheWrite5mTokens: Nothing
  , cacheWrite1hTokens: Nothing
  }

-- | Parse usage JSON (FFI boundary)
foreign import parseUsageJson :: String -> OpenAIUsage

-- | OpenAI usage format
type OpenAIUsage =
  { inputTokens :: Maybe Int
  , outputTokens :: Maybe Int
  , reasoningTokens :: Maybe Int
  , cacheReadTokens :: Maybe Int
  }

-- | Helper: fromMaybe
fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe default Nothing = default
fromMaybe _ (Just x) = x
