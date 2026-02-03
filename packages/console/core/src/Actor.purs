-- | Actor Module
-- |
-- | Provides actor context for request authentication and authorization.
-- | Actors represent the entity making a request (Account, User, System, Public).
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/actor.ts
module Forge.Console.Core.Actor
  ( ActorType(..)
  , ActorInfo
  , AccountActor
  , UserActor
  , SystemActor
  , PublicActor
  , UserRole(..)
  , ActorContext
  , use
  , provide
  , assert
  , assertAdmin
  , workspace
  , account
  , userID
  , userRole
  , createContext
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Forge.Console.Core.Util.Log as Log

-- | User roles within a workspace
data UserRole
  = Admin
  | Member

derive instance eqUserRole :: Eq UserRole

instance showUserRole :: Show UserRole where
  show Admin = "admin"
  show Member = "member"

-- | Actor types
data ActorType
  = AccountType
  | UserType
  | SystemType
  | PublicType

derive instance eqActorType :: Eq ActorType

instance showActorType :: Show ActorType where
  show AccountType = "account"
  show UserType = "user"
  show SystemType = "system"
  show PublicType = "public"

-- | Account actor properties
type AccountActor =
  { accountID :: String
  , email :: String
  }

-- | User actor properties
type UserActor =
  { userID :: String
  , workspaceID :: String
  , accountID :: String
  , role :: UserRole
  }

-- | System actor properties
type SystemActor =
  { workspaceID :: String
  }

-- | Public actor properties (no authentication)
type PublicActor = {}

-- | Actor info union type
-- | Represents any type of actor that can make a request
data ActorInfo
  = Account AccountActor
  | User UserActor
  | System SystemActor
  | Public PublicActor

derive instance eqActorInfo :: Eq ActorInfo

instance showActorInfo :: Show ActorInfo where
  show (Account a) = "Account(" <> a.accountID <> ")"
  show (User u) = "User(" <> u.userID <> ")"
  show (System s) = "System(" <> s.workspaceID <> ")"
  show (Public _) = "Public"

-- | Get actor type from info
actorType :: ActorInfo -> ActorType
actorType (Account _) = AccountType
actorType (User _) = UserType
actorType (System _) = SystemType
actorType (Public _) = PublicType

-- | Actor context container
type ActorContext =
  { ref :: Ref (Maybe ActorInfo)
  }

-- | Create a new actor context
createContext :: Effect ActorContext
createContext = do
  ref <- Ref.new Nothing
  pure { ref }

-- | Use the current actor
-- | Throws if no actor is provided
use :: ActorContext -> Effect ActorInfo
use ctx = do
  maybeActor <- Ref.read ctx.ref
  case maybeActor of
    Nothing -> throw "Actor context not provided"
    Just actor -> pure actor

-- | Provide an actor for the duration of a callback
provide :: forall a. ActorContext -> ActorInfo -> Effect a -> Effect a
provide ctx actor callback = do
  previous <- Ref.read ctx.ref
  Ref.write (Just actor) ctx.ref
  logger <- Log.create
  let taggedLogger = Log.tag "actor" (show actor) logger
  Log.info "provided" taggedLogger
  result <- callback
  Ref.write previous ctx.ref
  pure result

-- | Assert that the current actor is of a specific type
assert :: ActorContext -> ActorType -> Effect ActorInfo
assert ctx expectedType = do
  actor <- use ctx
  if actorType actor == expectedType
    then pure actor
    else throw $ "Expected actor type " <> show expectedType <> ", got " <> show (actorType actor)

-- | Assert that the current user is an admin
assertAdmin :: ActorContext -> Effect Unit
assertAdmin ctx = do
  actor <- use ctx
  case actor of
    User u -> 
      if u.role == Admin
        then pure unit
        else throw "Action not allowed. Ask your workspace admin to perform this action."
    _ -> throw "Expected user actor for admin assertion"

-- | Get the workspace ID from the current actor
workspace :: ActorContext -> Effect String
workspace ctx = do
  actor <- use ctx
  case actor of
    User u -> pure u.workspaceID
    System s -> pure s.workspaceID
    _ -> throw $ "Actor of type " <> show (actorType actor) <> " is not associated with a workspace"

-- | Get the account ID from the current actor
account :: ActorContext -> Effect String
account ctx = do
  actor <- use ctx
  case actor of
    Account a -> pure a.accountID
    User u -> pure u.accountID
    _ -> throw $ "Actor of type " <> show (actorType actor) <> " is not associated with an account"

-- | Get the user ID from the current actor
userID :: ActorContext -> Effect String
userID ctx = do
  actor <- assert ctx UserType
  case actor of
    User u -> pure u.userID
    _ -> throw "Unexpected: assert UserType returned non-user"

-- | Get the user role from the current actor
userRole :: ActorContext -> Effect UserRole
userRole ctx = do
  actor <- assert ctx UserType
  case actor of
    User u -> pure u.role
    _ -> throw "Unexpected: assert UserType returned non-user"
