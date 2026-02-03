-- | Provider Module
-- |
-- | BYOK (Bring Your Own Key) provider credential management.
-- | Stores and manages API credentials for external AI providers.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/provider.ts
module Forge.Console.Core.Provider
  ( list
  , create
  , remove
  , CreateInput
  , RemoveInput
  , ProviderName(..)
  , ListQuery
  , CreateResult
  ) where

import Prelude

import Data.Either (Either(..))
import Forge.Console.Core.Identifier as Identifier
import Forge.Console.Core.Actor (ActorInfo(..), UserRole(..))

-- | Supported provider names
data ProviderName
  = OpenAI
  | Anthropic
  | Google
  | Custom String

derive instance eqProviderName :: Eq ProviderName

instance showProviderName :: Show ProviderName where
  show OpenAI = "openai"
  show Anthropic = "anthropic"
  show Google = "google"
  show (Custom s) = s

-- | Query representation for list
type ListQuery =
  { table :: String
  , workspaceId :: String
  }

-- | Result of provider creation
type CreateResult =
  { providerId :: String
  }

-- | Input for creating a provider
type CreateInput =
  { provider :: ProviderName
  , credentials :: String
  , actor :: ActorInfo
  , workspaceId :: String
  , timestamp :: Int
  , random :: Array Int
  }

-- | Input for removing a provider
type RemoveInput =
  { provider :: ProviderName
  , actor :: ActorInfo
  }

-- | List providers (pure query representation)
list :: String -> ListQuery
list workspaceId = { table: "provider", workspaceId }

-- | Create or update a BYOK provider credential
-- | Requires admin role
create :: CreateInput -> Either String CreateResult
create input = 
  case input.actor of
    User u -> 
      if u.role == Admin
        then 
          let providerId = Identifier.toString $ Identifier.create Identifier.Provider
                { timestamp: input.timestamp, random: input.random }
          in Right { providerId }
        else Left "Only admins can create providers"
    _ -> Left "Only user actors can create providers"

-- | Remove a BYOK provider credential
-- | Requires admin role
remove :: RemoveInput -> Either String Unit
remove input = 
  case input.actor of
    User u -> 
      if u.role == Admin
        then Right unit
        else Left "Only admins can remove providers"
    _ -> Left "Only user actors can remove providers"
