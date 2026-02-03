-- | Model Schema
-- |
-- | Database schema for disabled models per workspace.
-- | Tracks which AI models are disabled for a workspace.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/schema/model.sql.ts
module Forge.Console.Core.Schema.Model
  ( Model
  , ModelId
  ) where

import Prelude

import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Forge.Console.Core.Schema.Types (ULID)
import Forge.Console.Core.Schema.Workspace (WorkspaceId)

-- | Model ID type
type ModelId = ULID

-- | Model entity (represents a disabled model)
type Model =
  { workspaceID :: WorkspaceId
  , id :: ModelId
  , model :: String            -- Model identifier (e.g., "claude-3-opus")
  , timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }
