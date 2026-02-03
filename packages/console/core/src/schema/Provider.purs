-- | Provider Schema
-- |
-- | Database schema for provider credentials.
-- | Stores BYOK (Bring Your Own Key) provider credentials per workspace.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/schema/provider.sql.ts
module Forge.Console.Core.Schema.Provider
  ( Provider
  , ProviderId
  ) where

import Prelude

import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Forge.Console.Core.Schema.Types (ULID)
import Forge.Console.Core.Schema.Workspace (WorkspaceId)

-- | Provider ID type
type ProviderId = ULID

-- | Provider entity
type Provider =
  { workspaceID :: WorkspaceId
  , id :: ProviderId
  , provider :: String         -- Provider name (openai, anthropic, google)
  , credentials :: String      -- API key (encrypted)
  , timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }
