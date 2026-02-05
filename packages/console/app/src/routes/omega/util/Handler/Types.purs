-- | Omega Handler Types
-- | Internal types for the Omega API request handler
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/handler.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Handler.Types
  ( RetryOptions
  , AuthInfo
  , ModelInfo
  , ProviderData
  , BillingSource(..)
  , CostInfo
  , mkRetryOptions
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Foreign (Foreign)
import Console.Core.Identifier (WorkspaceId, UserId)
import Console.Core.Util.Price (MicroCents)
import Console.App.Routes.Omega.Util.Provider.Provider (UsageInfo)

-- | Retry options for provider selection
type RetryOptions =
  { excludeProviders :: Array String
  , retryCount :: Int
  }

-- | Create retry options
mkRetryOptions :: Array String -> Int -> RetryOptions
mkRetryOptions excludeProviders retryCount =
  { excludeProviders, retryCount }

-- | Billing source type
data BillingSource
  = Anonymous
  | Free
  | Subscription
  | Balance

derive instance eqBillingSource :: Eq BillingSource

instance showBillingSource :: Show BillingSource where
  show Anonymous = "anonymous"
  show Free = "free"
  show Subscription = "subscription"
  show Balance = "balance"

-- | Authentication information
type AuthInfo =
  { apiKeyId :: String
  , workspaceID :: WorkspaceId
  , billing ::
      { balance :: MicroCents
      , paymentMethodID :: Maybe String
      , monthlyLimit :: Maybe Int  -- dollars
      , monthlyUsage :: Maybe MicroCents
      , timeMonthlyUsageUpdated :: Maybe Date
      , reloadTrigger :: Maybe Int  -- dollars
      , timeReloadLockedTill :: Maybe Date
      , subscription :: Maybe
          { plan :: String
          , useBalance :: Boolean
          }
      }
  , user ::
      { id :: UserId
      , monthlyLimit :: Maybe Int  -- dollars
      , monthlyUsage :: Maybe MicroCents
      , timeMonthlyUsageUpdated :: Maybe Date
      }
  , subscription :: Maybe
      { id :: String
      , rollingUsage :: Maybe MicroCents
      , fixedUsage :: Maybe MicroCents
      , timeRollingUpdated :: Maybe Date
      , timeFixedUpdated :: Maybe Date
      }
  , provider :: Maybe
      { credentials :: String
      }
  , isFree :: Boolean
  , isDisabled :: Boolean
  }


-- | Model information
type ModelInfo =
  { id :: String
  , formatFilter :: Maybe String  -- format required for this model variant
  , providers :: Array ProviderData
  , byokProvider :: Maybe String
  , trial :: Maybe
      { provider :: String
      }
  , rateLimit :: Maybe Int
  , stickyProvider :: Maybe String  -- "strict" | provider ID | null
  , fallbackProvider :: Maybe String
  , allowAnonymous :: Boolean
  , cost ::
      { input :: Number  -- per 1M tokens
      , output :: Number  -- per 1M tokens
      , cacheRead :: Maybe Number
      , cacheWrite5m :: Maybe Number
      , cacheWrite1h :: Maybe Number
      }
  , cost200K :: Maybe
      { input :: Number
      , output :: Number
      , cacheRead :: Maybe Number
      , cacheWrite5m :: Maybe Number
      , cacheWrite1h :: Maybe Number
      }
  }

-- | Provider helper methods (from provider helper functions)
type ProviderHelperMethods =
  { modifyUrl :: String -> Maybe Boolean -> String
  , modifyHeaders :: String -> String -> Unit  -- body, apiKey (headers accessed via global)  -- headersJson, bodyJson, apiKey -> mutates headers
  , modifyBody :: String -> String  -- JSON string in/out
  , createBinaryStreamDecoder :: Unit -> Maybe (String -> Maybe String)  -- Uint8Array decoder
  , streamSeparator :: String
  , createUsageParser :: Unit -> UsageParser
  , normalizeUsage :: String -> UsageInfo  -- JSON usage -> UsageInfo
  }

-- | Usage parser type
type UsageParser =
  { parse :: String -> Unit
  , retrieve :: Unit -> Maybe String  -- Returns JSON string of usage
  }

-- | Provider data (static configuration + helper methods)
type ProviderData =
  { id :: String
  , format :: String  -- "anthropic" | "openai" | "oa-compat" | "google"
  , api :: String  -- base API URL
  , model :: String  -- provider-specific model name
  , weight :: Maybe Int  -- for weighted selection
  , disabled :: Boolean
  , headerMappings :: Maybe (Record String String)  -- map header names
  , streamSeparator :: String  -- separator for streaming responses
  , storeModel :: String  -- model identifier for storage
  , apiKey :: String  -- API key for the provider
  , modifyUrl :: String -> Maybe Boolean -> String
  , modifyHeaders :: String -> String -> Unit  -- body, apiKey (headers accessed via global)
  , modifyBody :: String -> String
  , createBinaryStreamDecoder :: Unit -> Maybe (String -> Maybe String)
  , createUsageParser :: Unit -> UsageParser
  , normalizeUsage :: String -> UsageInfo
  }

-- | Cost information
type CostInfo =
  { costInMicroCents :: MicroCents
  }

-- | Date type (from FFI - JavaScript Date)
foreign import data Date :: Type
