-- | Role-Based Access Control (RBAC) - Authorization System
-- |
-- | **What:** Implements role-based access control for authorization decisions.
-- |         Defines roles, permissions, and checks if users have required permissions.
-- | **Why:** Provides fine-grained access control based on user roles. Enables
-- |         authorization decisions without database lookups (roles in JWT claims).
-- | **How:** Defines role hierarchy and permission mappings. Checks user roles
-- |         against required permissions for operations.
-- |
-- | **Dependencies:**
-- | - `Bridge.Auth.JWT`: JWT claims extraction
-- | - `Bridge.FFI.Node.Pino`: Structured logging
-- |
-- | **Mathematical Foundation:**
-- | - **Role Hierarchy:** `admin > moderator > user > guest`
-- | - **Permission Inheritance:** Higher roles inherit permissions from lower roles
-- | - **Authorization:** User authorized iff `hasPermission(userRoles, requiredPermission)`
-- |
-- | **Security Properties:**
-- | - Roles cannot be escalated without re-authentication
-- | - Permissions checked on every operation
-- | - Role hierarchy enforced
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Auth.RBAC as RBAC
-- |
-- | -- Check permission
-- | hasAccess <- RBAC.hasPermission claims.roles "venice.chat"
-- | if hasAccess then
-- |   -- Allow operation
-- | else
-- |   -- Deny operation
-- | ```
module Bridge.Auth.RBAC where

import Prelude
import Data.Array (elem, any, foldMap, mapMaybe, uncons)
import Data.Maybe (Maybe(..))
import Bridge.Auth.JWT (Claims)

-- | Role type
data Role = Admin | Moderator | User | Guest

derive instance eqRole :: Eq Role
derive instance ordRole :: Ord Role

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
roleToString Admin = "admin"
roleToString Moderator = "moderator"
roleToString User = "user"
roleToString Guest = "guest"

-- | Permission mapping: role -> permissions
rolePermissions :: Role -> Array Permission
rolePermissions Admin = [
  "venice.chat"
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
rolePermissions Moderator = [
  "venice.chat"
  , "venice.models"
  , "venice.image"
  , "lean.check"
  , "lean.goals"
  , "session.create"
  , "snapshot.create"
  , "snapshot.restore"
]
rolePermissions User = [
  "venice.chat"
  , "venice.models"
  , "lean.check"
  , "session.create"
  , "snapshot.create"
]
rolePermissions Guest = [
  "lean.check"
]

-- | Check if user has permission
-- |
-- | **Purpose:** Determines if user with given roles has required permission.
-- | **Parameters:**
-- | - `userRoles`: Array of role strings from JWT claims
-- | - `permission`: Required permission identifier
-- | **Returns:** True if user has permission, false otherwise
-- |
-- | **Logic:**
-- | - Parse roles from strings
-- | - Check if any role has the permission
-- | - Admin role has all permissions
hasPermission :: Array String -> Permission -> Boolean
hasPermission userRoles permission = do
  let parsedRoles = mapMaybe parseRole userRoles
  any (\role -> elem permission (rolePermissions role) || role == Admin) parsedRoles

-- | Check if user has any of the permissions
-- |
-- | **Purpose:** Checks if user has at least one of the required permissions.
-- | **Parameters:**
-- | - `userRoles`: Array of role strings
-- | - `permissions`: Array of permission identifiers
-- | **Returns:** True if user has any permission
hasAnyPermission :: Array String -> Array Permission -> Boolean
hasAnyPermission userRoles permissions = do
  any (hasPermission userRoles) permissions

-- | Check if user has all permissions
-- |
-- | **Purpose:** Checks if user has all required permissions.
-- | **Parameters:**
-- | - `userRoles`: Array of role strings
-- | - `permissions`: Array of permission identifiers
-- | **Returns:** True if user has all permissions
hasAllPermissions :: Array String -> Array Permission -> Boolean
hasAllPermissions userRoles permissions = do
  all (hasPermission userRoles) permissions
  where
    all :: forall a. (a -> Boolean) -> Array a -> Boolean
    all p arr = not (any (not <<< p) arr)

-- | Get user's effective permissions
-- |
-- | **Purpose:** Returns all permissions granted to user based on roles.
-- | **Parameters:**
-- | - `userRoles`: Array of role strings
-- | **Returns:** Array of permission identifiers
getEffectivePermissions :: Array String -> Array Permission
getEffectivePermissions userRoles = do
  let parsedRoles = mapMaybe parseRole userRoles
  let allPermissions = foldMap rolePermissions parsedRoles
  -- Remove duplicates
  nub allPermissions
  where
    nub :: forall a. Eq a => Array a -> Array a
    nub arr = go [] arr
      where
        go acc arr' = case uncons arr' of
          Nothing -> acc
          Just { head: x, tail: xs } -> if elem x acc then go acc xs else go (acc <> [x]) xs

-- | Check if user has minimum role level
-- |
-- | **Purpose:** Verifies user has at least the required role level.
-- | **Parameters:**
-- | - `userRoles`: Array of role strings
-- | - `minimumRole`: Minimum required role
-- | **Returns:** True if user has sufficient role level
hasMinimumRole :: Array String -> Role -> Boolean
hasMinimumRole userRoles minimumRole = do
  let parsedRoles = mapMaybe parseRole userRoles
  let minLevel = roleHierarchy minimumRole
  any (\role -> roleHierarchy role >= minLevel) parsedRoles

-- | Authorization result
type AuthorizationResult =
  { authorized :: Boolean
  , reason :: Maybe String
  }

-- | Authorize operation
-- |
-- | **Purpose:** Checks if user is authorized for an operation.
-- | **Parameters:**
-- | - `claims`: JWT claims with user roles
-- | - `permission`: Required permission
-- | **Returns:** Authorization result
authorize :: Claims -> Permission -> AuthorizationResult
authorize claims permission = do
  if hasPermission claims.roles permission then
    { authorized: true, reason: Nothing }
  else
    { authorized: false, reason: Just ("User lacks permission: " <> permission) }
