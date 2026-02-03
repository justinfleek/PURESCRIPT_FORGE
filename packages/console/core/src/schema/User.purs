-- | User Schema
-- |
-- | Database schema for user entities.
-- | Users belong to workspaces and have roles (admin/member).
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/schema/user.sql.ts
module Forge.Console.Core.Schema.User
  ( User
  , UserId
  , UserRole(..)
  , allUserRoles
  ) where

import Prelude

import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Forge.Console.Core.Schema.Types (ULID)
import Forge.Console.Core.Schema.Workspace (WorkspaceId)
import Forge.Console.Core.Schema.Account (AccountId)

-- | User ID type
type UserId = ULID

-- | User roles
data UserRole
  = Admin
  | Member

derive instance eqUserRole :: Eq UserRole

instance showUserRole :: Show UserRole where
  show Admin = "admin"
  show Member = "member"

-- | All valid user roles
allUserRoles :: Array UserRole
allUserRoles = [Admin, Member]

-- | User entity
type User =
  { workspaceID :: WorkspaceId
  , id :: UserId
  , accountID :: Maybe AccountId  -- Null if invited but not yet joined
  , email :: Maybe String         -- Set if invited by email
  , name :: String
  , timeSeen :: Maybe DateTime
  , color :: Maybe Int
  , role :: UserRole
  , monthlyLimit :: Maybe Int
  , monthlyUsage :: Maybe Int
  , timeMonthlyUsageUpdated :: Maybe DateTime
  , timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }
