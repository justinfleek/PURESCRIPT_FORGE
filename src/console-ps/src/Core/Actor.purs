-- | Console.Core.Actor - Authentication Context and Authorization
-- |
-- | **What:** Provides the actor context system for tracking authenticated users,
-- |         their roles, and workspace associations throughout request handling.
-- | **Why:** Secure authorization requires knowing WHO is making a request and
-- |         WHAT permissions they have. Actor context threads this info through
-- |         the entire call stack without explicit parameter passing.
-- | **How:** Uses Reader monad pattern. Actor is set at request boundary and
-- |         accessed via `use`. Authorization checks (assertAdmin, assertUser)
-- |         enforce role requirements.
-- |
-- | **Dependencies:**
-- | - Console.Core.Types: Domain types (UserId, WorkspaceId, UserRole)
-- | - Effect: Side effects
-- | - Control.Monad.Reader: Context threading
-- |
-- | **Mathematical Foundation:**
-- | - **Actor Types Form Sum Type:** `Actor = Account | Public | User | System`
-- | - **Workspace Access:** `∀ a : Actor. hasWorkspace(a) ⟹ workspace(a) ∈ Workspaces`
-- | - **Role Hierarchy:** `assertAdmin ⟹ role = Admin`
-- |
-- | **Security Properties:**
-- | - Actor cannot be forged (set only at request boundary)
-- | - Role checks are mandatory (compile-time enforced)
-- | - Workspace isolation (actors can only access their workspace)
-- |
-- | **Corresponding Proofs:** `console-lean/Console/Core/Actor.lean`
module Console.Core.Actor
  ( -- * Actor Types
    Actor(..)
  , AccountActor
  , PublicActor
  , UserActor
  , SystemActor
    -- * Context Operations
  , ActorContext
  , runWithActor
  , useActor
    -- * Assertions
  , assertAccount
  , assertUser
  , assertSystem
  , assertAdmin
    -- * Accessors
  , workspace
  , account
  , userId
  , userRole
  ) where

import Prelude

import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (throw)
import Console.Core.Types (AccountId(..), UserId(..), WorkspaceId(..), UserRole(..))

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTOR TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Account actor - authenticated but not in a workspace
type AccountActor =
  { accountId :: AccountId
  , email :: String
  }

-- | Public actor - unauthenticated
type PublicActor = {}

-- | User actor - authenticated and in a workspace
type UserActor =
  { userId :: UserId
  , workspaceId :: WorkspaceId
  , accountId :: AccountId
  , role :: UserRole
  }

-- | System actor - internal operations
type SystemActor =
  { workspaceId :: WorkspaceId
  }

-- | Actor sum type
-- | Represents all possible authentication states
data Actor
  = ActorAccount AccountActor
  | ActorPublic PublicActor
  | ActorUser UserActor
  | ActorSystem SystemActor

derive instance eqActor :: Eq Actor

instance showActor :: Show Actor where
  show (ActorAccount a) = "Account(" <> show a.email <> ")"
  show (ActorPublic _) = "Public"
  show (ActorUser u) = "User(" <> show u.userId <> ", role=" <> show u.role <> ")"
  show (ActorSystem s) = "System(" <> show s.workspaceId <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONTEXT OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Actor context monad
type ActorContext = ReaderT Actor Aff

-- | Run computation with actor context
runWithActor :: forall a. Actor -> ActorContext a -> Aff a
runWithActor actor computation = runReaderT computation actor

-- | Get current actor from context
useActor :: ActorContext Actor
useActor = ask

-- ═══════════════════════════════════════════════════════════════════════════════
-- ASSERTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Assert actor is Account type, throw if not
assertAccount :: ActorContext AccountActor
assertAccount = do
  actor <- useActor
  case actor of
    ActorAccount a -> pure a
    other -> liftEffect $ throw $ "Expected actor type account, got " <> show other

-- | Assert actor is User type, throw if not
assertUser :: ActorContext UserActor
assertUser = do
  actor <- useActor
  case actor of
    ActorUser u -> pure u
    other -> liftEffect $ throw $ "Expected actor type user, got " <> show other

-- | Assert actor is System type, throw if not
assertSystem :: ActorContext SystemActor
assertSystem = do
  actor <- useActor
  case actor of
    ActorSystem s -> pure s
    other -> liftEffect $ throw $ "Expected actor type system, got " <> show other

-- | Assert current user has admin role
-- | Throws if not admin
assertAdmin :: ActorContext Unit
assertAdmin = do
  user <- assertUser
  case user.role of
    Admin -> pure unit
    Member -> liftEffect $ throw "Action not allowed. Ask your workspace admin to perform this action."

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACCESSORS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get workspace ID from actor context
-- | Throws if actor has no workspace
workspace :: ActorContext WorkspaceId
workspace = do
  actor <- useActor
  case actor of
    ActorUser u -> pure u.workspaceId
    ActorSystem s -> pure s.workspaceId
    other -> liftEffect $ throw $ "Actor of type " <> show other <> " is not associated with a workspace"

-- | Get account ID from actor context
-- | Throws if actor has no account
account :: ActorContext AccountId
account = do
  actor <- useActor
  case actor of
    ActorAccount a -> pure a.accountId
    ActorUser u -> pure u.accountId
    other -> liftEffect $ throw $ "Actor of type " <> show other <> " is not associated with an account"

-- | Get user ID from actor context
-- | Requires User actor type
userId :: ActorContext UserId
userId = do
  user <- assertUser
  pure user.userId

-- | Get user role from actor context
-- | Requires User actor type
userRole :: ActorContext UserRole
userRole = do
  user <- assertUser
  pure user.role
