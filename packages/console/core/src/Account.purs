-- | Account Module
-- |
-- | Account management operations.
-- | Accounts are the top-level identity entities.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/account.ts
module Forge.Console.Core.Account
  ( create
  , fromID
  , CreateInput
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Forge.Console.Core.Identifier as Identifier
import Forge.Console.Core.Schema.Account (Account, AccountId)
import Forge.Console.Core.Drizzle.Database as Database

-- | Input for creating an account
type CreateInput =
  { id :: Maybe AccountId
  , timestamp :: Int
  , random :: Array Int
  }

-- | Create a new account
-- | Optionally accepts a pre-generated ID
create :: CreateInput -> Either String AccountId
create input = 
  let 
    accountId = case input.id of
      Just id -> Identifier.fromString id
      Nothing -> Identifier.create Identifier.Account 
        { timestamp: input.timestamp, random: input.random }
    idStr = Identifier.toString accountId
  in Right idStr

-- | Get account by ID (pure query representation)
fromID :: AccountId -> { table :: String, id :: AccountId }
fromID id = 
  { table: "account"
  , id: id
  }
