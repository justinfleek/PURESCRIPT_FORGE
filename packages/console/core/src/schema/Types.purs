-- | Schema Types Module
-- |
-- | Common type definitions for database schemas.
-- | Provides timestamps, ULID columns, and workspace column patterns.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/drizzle/types.ts
module Forge.Console.Core.Schema.Types
  ( Timestamps
  , WorkspaceColumns
  , ULID
  , UTC
  ) where

import Prelude

import Data.DateTime (DateTime)
import Data.Maybe (Maybe)

-- | ULID identifier type
type ULID = String

-- | UTC timestamp type
type UTC = DateTime

-- | Standard timestamps for all entities
type Timestamps =
  { timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }

-- | Standard workspace-scoped columns
type WorkspaceColumns =
  { workspaceID :: ULID
  , id :: ULID
  }
