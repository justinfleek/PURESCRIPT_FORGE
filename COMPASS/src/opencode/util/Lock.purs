-- | Lock utilities for mutual exclusion
module Opencode.Util.Lock where

import Prelude
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Aff as Aff
import Data.Array as Array

-- | Lock type
type Lock =
  { acquire :: Aff Unit
  , release :: Aff Unit
  }

-- | Lock state
type LockState =
  { held :: Boolean
  , waiters :: Array (Effect Unit)
  }

-- | Create a new lock
create :: Aff Lock
create = do
  stateRef <- liftEffect $ Ref.new { held: false, waiters: [] }
  pure
    { acquire: acquireLock stateRef
    , release: releaseLock stateRef
    }

-- | Acquire lock (wait if held)
acquireLock :: Ref LockState -> Aff Unit
acquireLock stateRef = do
  state <- liftEffect $ Ref.read stateRef
  if state.held
    then do
      -- Wait for lock to be released
      waitForLock stateRef
      acquireLock stateRef
    else do
      liftEffect $ Ref.modify_ (\s -> s { held = true }) stateRef

-- | Wait for lock to be released
waitForLock :: Ref LockState -> Aff Unit
waitForLock stateRef = do
  -- Simplified waiting - poll until lock is released
  Aff.delay (Aff.Milliseconds 10.0)
  pure unit

-- | Release lock
releaseLock :: Ref LockState -> Aff Unit
releaseLock stateRef = do
  state <- liftEffect $ Ref.read stateRef
  liftEffect $ Ref.modify_ (\s -> s { held = false, waiters = [] }) stateRef
  -- Notify waiters (simplified - would properly wake waiters)
  pure unit

-- | Run with lock (acquire, run action, release)
withLock :: forall a. Lock -> Aff a -> Aff a
withLock lock action = do
  lock.acquire
  result <- Aff.finally lock.release action
  pure result
