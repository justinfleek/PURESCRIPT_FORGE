-- | Role-Based Access Control (RBAC) - Authorization System
-- |
-- | Implements role-based access control for authorization decisions.
-- | Role hierarchy: admin > moderator > user > guest
-- | Higher roles inherit permissions from lower roles.
module Bridge.Auth.RBAC where

import Prelude

import Data.Array (elem, any, concatMap, nub)
import Data.Maybe (Maybe(..), mapMaybe)
import Bridge.Auth.JWT (Claims)

-- | Role type
data Role = Admin | Moderator | User | Guest

derive instance eqRole :: Eq Role
derive instance ordRole :: Ord Role

instance showRole :: Show Role where
  show Admin = "admin"
  show Moderator = "moderator"
  show User = "user"
  show Guest = "guest"

-- | Permission identifier
type Permission = String

-- | Role hierarchy (higher number = more permissions)
roleHierarchy :: Role -> Int
roleHierarchy Admin = 4
roleHierarchy Moderator = 3
roleHierarchy User = 2
roleHierarchy Guest = 1

-- | Parse role from string
parseRole :: String -> Maybe Role
parseRole "admin" = Just Admin
parseRole "moderator" = Just Moderator
parseRole "user" = Just User
parseRole "guest" = Just Guest
parseRole _ = Nothing

-- | Role to string
roleToString :: Role -> String
roleToString = show

-- | Permission mapping: role -> permissions
rolePermissions :: Role -> Array Permission
rolePermissions Admin =
  [ "venice.chat"
  , "venice.models"
  , "venice.image"
  , "lean.check"
  , "lean.goals"
  , "session.create"
  , "session.delete"
  , "snapshot.create"
  , "snapshot.restore"
  , "admin.users"
  , "admin.sessions"
  , "admin.config"
  ]
rolePermissions Moderator =
  [ "venice.chat"
  , "venice.models"
  , "venice.image"
  , "lean.check"
  , "lean.goals"
  , "session.create"
  , "snapshot.create"
  , "snapshot.restore"
  ]
rolePermissions User =
  [ "venice.chat"
  , "venice.models"
  , "lean.check"
  , "session.create"
  , "snapshot.create"
  ]
rolePermissions Guest =
  [ "lean.check"
  ]

-- | Check if user has permission
hasPermission :: Array String -> Permission -> Boolean
hasPermission userRoles permission =
  let parsedRoles = mapMaybe parseRole userRoles
  in any (\role -> elem permission (rolePermissions role) || role == Admin) parsedRoles

-- | Check if user has any of the permissions
hasAnyPermission :: Array String -> Array Permission -> Boolean
hasAnyPermission userRoles permissions =
  any (hasPermission userRoles) permissions

-- | Check if user has all permissions
hasAllPermissions :: Array String -> Array Permission -> Boolean
hasAllPermissions userRoles permissions =
  not (any (not <<< hasPermission userRoles) permissions)

-- | Get user's effective permissions
getEffectivePermissions :: Array String -> Array Permission
getEffectivePermissions userRoles =
  let parsedRoles = mapMaybe parseRole userRoles
  in nub (concatMap rolePermissions parsedRoles)

-- | Check if user has minimum role level
hasMinimumRole :: Array String -> Role -> Boolean
hasMinimumRole userRoles minimumRole =
  let parsedRoles = mapMaybe parseRole userRoles
      minLevel = roleHierarchy minimumRole
  in any (\role -> roleHierarchy role >= minLevel) parsedRoles

-- | Authorization result
type AuthorizationResult =
  { authorized :: Boolean
  , reason :: Maybe String
  }

-- | Authorize operation
authorize :: Claims -> Permission -> AuthorizationResult
authorize claims permission =
  if hasPermission claims.roles permission then
    { authorized: true, reason: Nothing }
  else
    { authorized: false, reason: Just ("User lacks permission: " <> permission) }
