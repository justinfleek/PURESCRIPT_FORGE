-- | Test Helpers
-- | Utility functions for testing
module Test.Bridge.Utils.TestHelpers where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, delay, Milliseconds(..))
import Data.Maybe (Maybe(..))
import Bridge.State.Store (StateStore, createStore, AppState)

-- | Wait for condition with timeout
-- | Returns true if condition becomes true within timeout, false otherwise
waitFor :: (Effect Boolean) -> Int -> Aff Boolean
waitFor condition timeoutMs = do
  let maxIterations = timeoutMs / 10
  waitForIteration condition maxIterations 0
  where
    waitForIteration :: (Effect Boolean) -> Int -> Int -> Aff Boolean
    waitForIteration cond maxIter currentIter = do
      if currentIter >= maxIter then
        pure false
      else do
        result <- liftEffect cond
        if result then
          pure true
        else do
          delay (Milliseconds 10.0)
          waitForIteration cond maxIter (currentIter + 1)

-- | Create test state store
createTestStore :: Effect StateStore
createTestStore = createStore

-- | Reset state store to initial state
resetStore :: StateStore -> Effect Unit
resetStore store = do
  initialState <- getInitialState
  write store.state initialState
  where
    write :: forall a. Ref a -> a -> Effect Unit
    write ref val = modify_ (\_ -> val) ref

-- | Assert state matches expected
assertState :: StateStore -> AppState -> Effect Boolean
assertState store expected = do
  current <- getState store
  pure (current == expected)

-- | Run test with cleanup
withCleanup :: forall a. Effect a -> Effect Unit -> Effect a
withCleanup test cleanup = do
  result <- test
  cleanup
  pure result

-- | Create test timeout
createTimeout :: Int -> Aff Unit
createTimeout ms = delay (Milliseconds (fromInt ms))

-- | Measure execution time
measureTime :: forall a. Effect a -> Effect { result :: a, duration :: Number }
measureTime action = do
  start <- getCurrentTimeMs
  result <- action
  end <- getCurrentTimeMs
  pure { result, duration: end - start }

-- | Assert performance threshold
assertPerformance :: Number -> Number -> Effect Boolean
assertPerformance actual threshold = pure (actual < threshold)

-- | Create test data with size
createTestData :: Int -> Effect String
createTestData size = do
  -- Generate test data of specified size
  pure (generateTestData size)

foreign import getState :: StateStore -> Effect AppState
foreign import getInitialState :: Effect AppState
foreign import modify_ :: forall a. (a -> a) -> Ref a -> Effect Unit
foreign import fromInt :: Int -> Number
foreign import getCurrentTimeMs :: Effect Number
foreign import generateTestData :: Int -> String

import Effect.Ref (Ref)
import Effect.Aff (Aff, delay, Milliseconds(..))
import Effect.Class (liftEffect)
