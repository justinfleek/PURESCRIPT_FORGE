-- | Provider management hook
-- | Migrated from forge-dev/packages/app/src/hooks/use-providers.ts
module Forge.App.Hooks.UseProviders
  ( ProviderInfo
  , ProvidersState
  , popularProviders
  , useProviders
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Array (filter, elem)
import Effect (Effect)

-- | Popular provider IDs
popularProviders :: Array String
popularProviders = 
  [ "forge"
  , "anthropic"
  , "github-copilot"
  , "openai"
  , "google"
  , "openrouter"
  , "vercel"
  ]

-- | Provider information
type ProviderInfo =
  { id :: String
  , name :: String
  , models :: Array ModelInfo
  }

type ModelInfo =
  { id :: String
  , name :: String
  , cost :: Maybe { input :: Number, output :: Number }
  }

-- | Provider store data
type ProviderStore =
  { all :: Array ProviderInfo
  , connected :: Array String
  , default :: Maybe String
  }

-- | Hook result
type ProvidersState =
  { all :: Array ProviderInfo
  , default :: Maybe String
  , popular :: Array ProviderInfo
  , connected :: Array ProviderInfo
  , paid :: Array ProviderInfo
  }

-- | Use providers hook (needs context integration)
useProviders :: ProviderStore -> ProvidersState
useProviders store =
  { all: store.all
  , default: store.default
  , popular: filter (\p -> elem p.id popularProviders) store.all
  , connected: filter (\p -> elem p.id store.connected) store.all
  , paid: filter isPaid (filter (\p -> elem p.id store.connected) store.all)
  }

-- Check if provider has paid models
isPaid :: ProviderInfo -> Boolean
isPaid provider
  | provider.id /= "forge" = true
  | otherwise = hasAnyPaidModel provider.models

hasAnyPaidModel :: Array ModelInfo -> Boolean
hasAnyPaidModel models = case filter hasCost models of
  [] -> false
  _ -> true
  where
  hasCost m = case m.cost of
    Just c | c.input > 0.0 -> true
    _ -> false
