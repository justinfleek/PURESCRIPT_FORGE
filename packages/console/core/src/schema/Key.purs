-- | Key Schema
-- |
-- | Database schema for API key entities.
-- | Keys belong to users within workspaces for API authentication.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/schema/key.sql.ts
module Forge.Console.Core.Schema.Key
  ( Key
  , KeyId
  , SecretKey
  ) where

import Prelude

import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Forge.Console.Core.Schema.Types (ULID)
import Forge.Console.Core.Schema.Workspace (WorkspaceId)
import Forge.Console.Core.Schema.User (UserId)

-- | Key ID type
type KeyId = ULID

-- | Secret key format: sk-{64 random chars}
type SecretKey = String

-- | Key entity
type Key =
  { workspaceID :: WorkspaceId
  , id :: KeyId
  , name :: String
  , key :: SecretKey
  , userID :: UserId
  , timeUsed :: Maybe DateTime
  , timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }
