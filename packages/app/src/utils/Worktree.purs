-- | Worktree state tracking for sandbox creation
-- | Migrated from: forge-dev/packages/app/src/utils/worktree.ts (74 lines)
module Sidepanel.Utils.Worktree
  ( Worktree
  , WorktreeState(..)
  , get
  , pending
  , ready
  , failed
  , wait
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect (Effect)
import Effect.Aff (Aff, makeAff)
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- | Worktree state
data WorktreeState
  = Pending
  | Ready
  | Failed String

derive instance eqWorktreeState :: Eq WorktreeState

-- | Module state
foreign import stateMap :: Ref (Map String WorktreeState)
foreign import waitersMap :: Ref (Map String (Deferred WorktreeState))

-- | Deferred promise type
type Deferred a =
  { promise :: Aff a
  , resolve :: a -> Effect Unit
  }

-- | Normalize directory path (remove trailing slashes)
normalize :: String -> String
normalize dir = 
  let stripped = String.dropWhile (_ == '/') $ String.reverse dir
  in String.reverse stripped

-- | Get current worktree state
get :: String -> Effect (Maybe WorktreeState)
get directory = do
  let key = normalize directory
  state <- Ref.read stateMap
  pure $ Map.lookup key state

-- | Mark worktree as pending
pending :: String -> Effect Unit
pending directory = do
  let key = normalize directory
  current <- get directory
  case current of
    Just Pending -> pure unit
    Just Ready -> pure unit
    Just (Failed _) -> pure unit
    Nothing -> Ref.modify (Map.insert key Pending) stateMap

-- | Mark worktree as ready
ready :: String -> Effect Unit
ready directory = do
  let key = normalize directory
  Ref.modify (Map.insert key Ready) stateMap
  resolveWaiter key Ready

-- | Mark worktree as failed
failed :: String -> String -> Effect Unit
failed directory message = do
  let key = normalize directory
      state = Failed message
  Ref.modify (Map.insert key state) stateMap
  resolveWaiter key state

-- | Resolve any waiting promises
resolveWaiter :: String -> WorktreeState -> Effect Unit
resolveWaiter key state = do
  waiters <- Ref.read waitersMap
  case Map.lookup key waiters of
    Nothing -> pure unit
    Just waiter -> do
      Ref.modify (Map.delete key) waitersMap
      waiter.resolve state

-- | Wait for worktree to reach a final state
-- | Returns immediately if already ready or failed
wait :: String -> Aff WorktreeState
wait directory = do
  let key = normalize directory
  currentState <- liftEffect $ get directory
  case currentState of
    Just Ready -> pure Ready
    Just (Failed msg) -> pure (Failed msg)
    _ -> do
      -- Check for existing waiter
      waiters <- liftEffect $ Ref.read waitersMap
      case Map.lookup key waiters of
        Just existing -> existing.promise
        Nothing -> do
          -- Create new deferred
          deferred <- makeDeferred
          liftEffect $ Ref.modify (Map.insert key deferred) waitersMap
          deferred.promise

-- | Create a deferred promise
makeDeferred :: forall a. Aff (Deferred a)
makeDeferred = makeAff \callback -> do
  -- Create a resolver that will be called when state changes
  resolverRef <- Ref.new (\_ -> pure unit)
  
  let deferred =
        { promise: makeAff \cb -> do
            Ref.write (\a -> cb (Right a)) resolverRef
            pure mempty
        , resolve: \a -> do
            resolver <- Ref.read resolverRef
            resolver a
        }
  
  callback (Right deferred)
  pure mempty

-- | Lift Effect to Aff
foreign import liftEffect :: forall a. Effect a -> Aff a

-- | Right constructor for Either
foreign import data Right :: forall a b. b -> Either a b
foreign import data Either :: Type -> Type -> Type
