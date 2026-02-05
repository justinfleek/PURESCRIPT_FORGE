-- | Context utilities
module Opencode.Util.Context where

import Prelude
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Data.Maybe (Maybe(..))
import Data.Map as Map

-- | Context storage (similar to AsyncLocalStorage in Node)
-- | Uses thread-local storage via Ref

-- | Global context storage
contextStorageRef :: Ref (Map.Map String String)
contextStorageRef = unsafePerformEffect $ Ref.new Map.empty
  where
    foreign import unsafePerformEffect :: forall a. Effect a -> a

-- | Get a value from context
-- | Note: This is a simplified implementation. In production, would use
-- | proper thread-local storage or Reader monad for type-safe context
get :: forall a. String -> Effect (Maybe a)
get key = do
  storage <- Ref.read contextStorageRef
  case Map.lookup key storage of
    Nothing -> pure Nothing
    Just value -> pure $ Just (unsafeCoerce value)
  where
    foreign import unsafeCoerce :: forall a b. a -> b

-- | Set a value in context
set :: forall a. String -> a -> Effect Unit
set key value = do
  Ref.modify_ (\storage -> Map.insert key (unsafeCoerce value) storage) contextStorageRef
  where
    foreign import unsafeCoerce :: forall a b. a -> b

-- | Run with context (sets context, runs action, restores previous)
runWith :: forall a b. String -> a -> Effect b -> Effect b
runWith key value action = do
  -- Save previous value
  previous <- get key
  
  -- Set new value
  set key value
  
  -- Run action and restore previous value
  result <- action
  case previous of
    Just prev -> set key prev
    Nothing -> do
      storage <- Ref.read contextStorageRef
      Ref.write (Map.delete key storage) contextStorageRef
  
  pure result
