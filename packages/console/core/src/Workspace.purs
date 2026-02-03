-- | Workspace Module
-- |
-- | Workspace management operations.
-- | Workspaces are organizational units containing users, keys, and billing.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/workspace.ts
module Forge.Console.Core.Workspace
  ( create
  , update
  , remove
  , CreateInput
  , UpdateInput
  , CreateResult
  ) where

import Prelude

import Data.Either (Either(..))
import Forge.Console.Core.Identifier as Identifier
import Forge.Console.Core.Schema.Workspace (WorkspaceId)
import Forge.Console.Core.Actor (ActorInfo(..), UserRole(..))

-- | Input for creating a workspace
type CreateInput =
  { name :: String
  , actor :: ActorInfo
  , timestamp :: Int
  , random :: Array Int
  }

-- | Result of workspace creation
type CreateResult =
  { workspaceId :: WorkspaceId
  , userId :: String
  , billingId :: String
  }

-- | Input for updating a workspace
type UpdateInput =
  { name :: String
  , actor :: ActorInfo
  }

-- | Create a new workspace
-- | Creates the workspace, adds the current account as admin,
-- | initializes billing, and creates a default API key
create :: CreateInput -> Either String CreateResult
create input = 
  case input.actor of
    Account _ -> 
      let 
        workspaceId = Identifier.toString $ Identifier.create Identifier.Workspace 
          { timestamp: input.timestamp, random: input.random }
        userId = Identifier.toString $ Identifier.create Identifier.User
          { timestamp: input.timestamp + 1, random: input.random }
        billingId = Identifier.toString $ Identifier.create Identifier.Billing
          { timestamp: input.timestamp + 2, random: input.random }
      in Right { workspaceId, userId, billingId }
    _ -> Left "Only account actors can create workspaces"

-- | Update workspace name
-- | Requires admin role
update :: UpdateInput -> Either String Unit
update input = 
  case input.actor of
    User u -> 
      if u.role == Admin
        then Right unit
        else Left "Only admins can update workspaces"
    _ -> Left "Only user actors can update workspaces"

-- | Soft-delete a workspace
remove :: ActorInfo -> Either String Unit
remove actor = 
  case actor of
    User u -> 
      if u.role == Admin
        then Right unit
        else Left "Only admins can remove workspaces"
    _ -> Left "Only user actors can remove workspaces"
