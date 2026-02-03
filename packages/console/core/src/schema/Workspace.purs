-- | Workspace Schema
-- |
-- | Database schema for workspace entities.
-- | Workspaces are organizational units containing users, keys, and billing.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/schema/workspace.sql.ts
module Forge.Console.Core.Schema.Workspace
  ( Workspace
  , WorkspaceId
  ) where

import Prelude

import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Forge.Console.Core.Schema.Types (ULID)

-- | Workspace ID type
type WorkspaceId = ULID

-- | Workspace entity
type Workspace =
  { id :: WorkspaceId
  , slug :: Maybe String
  , name :: String
  , timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }
