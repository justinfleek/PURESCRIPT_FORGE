-- | With Actor Context Helper
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/context/auth.withActor.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Context.AuthWithActor
  ( withActor
  , withActorM
  , WithActorResult(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Console.Core.Actor (ActorInfo(..), ActorType(..), provide)
import Console.App.Context.Auth (ActorResult(..), getActorFromSession, AuthSession)

-- | Result of withActor operation
data WithActorResult a
  = WithActorSuccess a
  | WithActorRedirect String
  | WithActorError String

derive instance functorWithActorResult :: Functor WithActorResult

instance applyWithActorResult :: Apply WithActorResult where
  apply (WithActorSuccess f) (WithActorSuccess a) = WithActorSuccess (f a)
  apply (WithActorRedirect url) _ = WithActorRedirect url
  apply _ (WithActorRedirect url) = WithActorRedirect url
  apply (WithActorError e) _ = WithActorError e
  apply _ (WithActorError e) = WithActorError e

instance applicativeWithActorResult :: Applicative WithActorResult where
  pure = WithActorSuccess

instance bindWithActorResult :: Bind WithActorResult where
  bind (WithActorSuccess a) f = f a
  bind (WithActorRedirect url) _ = WithActorRedirect url
  bind (WithActorError e) _ = WithActorError e

instance monadWithActorResult :: Monad WithActorResult

instance showWithActorResult :: Show a => Show (WithActorResult a) where
  show (WithActorSuccess a) = "(WithActorSuccess " <> show a <> ")"
  show (WithActorRedirect url) = "(WithActorRedirect " <> show url <> ")"
  show (WithActorError e) = "(WithActorError " <> show e <> ")"

-- | Execute a function with the actor context
-- | This is the pure version that takes pre-resolved actor info
withActor 
  :: forall a
   . ActorResult 
  -> (ActorInfo -> a) 
  -> WithActorResult a
withActor actorResult fn = case actorResult of
  ActorAccount props ->
    WithActorSuccess (fn (ActorInfo AccountActor props))
  
  ActorUser props ->
    WithActorSuccess (fn (ActorInfo UserActor props))
  
  ActorPublic ->
    WithActorSuccess (fn (ActorInfo PublicActor {}))
  
  ActorRedirect url ->
    WithActorRedirect url

-- | Monadic version for chaining operations
withActorM 
  :: forall a
   . ActorResult 
  -> (ActorInfo -> WithActorResult a) 
  -> WithActorResult a
withActorM actorResult fn = case actorResult of
  ActorAccount props ->
    fn (ActorInfo AccountActor props)
  
  ActorUser props ->
    fn (ActorInfo UserActor props)
  
  ActorPublic ->
    fn (ActorInfo PublicActor {})
  
  ActorRedirect url ->
    WithActorRedirect url

-- | Provide actor context using Reader pattern (pure)
-- | This matches the Actor.provide pattern from core
provideActor 
  :: forall a
   . ActorInfo 
  -> (ActorInfo -> a) 
  -> a
provideActor actor fn = fn actor

-- | Get actor from session and execute function
withActorFromSession
  :: forall a
   . AuthSession
  -> Maybe String  -- workspace
  -> Maybe { userId :: String, workspaceId :: String, accountId :: String, role :: String }
  -> (ActorInfo -> a)
  -> WithActorResult a
withActorFromSession session workspace userLookup fn =
  let actorResult = getActorFromSession session workspace userLookup
  in withActor actorResult fn
