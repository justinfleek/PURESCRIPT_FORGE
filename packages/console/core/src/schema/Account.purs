-- | Account Schema
-- |
-- | Database schema for account entities.
-- | Accounts are the top-level identity entities.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/schema/account.sql.ts
module Forge.Console.Core.Schema.Account
  ( Account
  , AccountId
  ) where

import Prelude

import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Forge.Console.Core.Schema.Types (ULID, Timestamps)

-- | Account ID type
type AccountId = ULID

-- | Account entity
type Account =
  { id :: AccountId
  , timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }
