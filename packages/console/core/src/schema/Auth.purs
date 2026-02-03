-- | Auth Schema
-- |
-- | Database schema for authentication records.
-- | Links accounts to identity providers (email, OAuth).
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/schema/auth.sql.ts
module Forge.Console.Core.Schema.Auth
  ( Auth
  , AuthId
  , AuthProvider(..)
  ) where

import Prelude

import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Forge.Console.Core.Schema.Types (ULID)
import Forge.Console.Core.Schema.Account (AccountId)

-- | Auth ID type
type AuthId = ULID

-- | Authentication providers
data AuthProvider
  = Email
  | GitHub
  | Google

derive instance eqAuthProvider :: Eq AuthProvider

instance showAuthProvider :: Show AuthProvider where
  show Email = "email"
  show GitHub = "github"
  show Google = "google"

-- | Auth entity
type Auth =
  { id :: AuthId
  , accountID :: AccountId
  , provider :: AuthProvider
  , subject :: String          -- Email or OAuth subject ID
  , timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }
