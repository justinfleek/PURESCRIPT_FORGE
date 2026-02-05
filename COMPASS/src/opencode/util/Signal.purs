-- | Signal utilities
module Opencode.Util.Signal where

import Prelude
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Data.Array as Array

-- | Signal type (reactive value)
type Signal a =
  { get :: Effect a
  , set :: a -> Effect Unit
  , subscribe :: (a -> Effect Unit) -> Effect (Effect Unit)
  }

-- | Internal signal state
type SignalState a =
  { value :: a
  , subscribers :: Array (a -> Effect Unit)
  }

-- | Create a signal with initial value
create :: forall a. a -> Effect (Signal a)
create initial = do
  stateRef <- Ref.new { value: initial, subscribers: [] }
  pure
    { get: do
        state <- Ref.read stateRef
        pure state.value
    , set: \newValue -> do
        state <- Ref.read stateRef
        Ref.write { value: newValue, subscribers: state.subscribers } stateRef
        -- Notify all subscribers
        Array.traverse_ (\sub -> sub newValue) state.subscribers
    , subscribe: \callback -> do
        state <- Ref.read stateRef
        Ref.modify_ (\s -> s { subscribers = Array.snoc s.subscribers callback }) stateRef
        -- Return unsubscribe function
        pure $ do
          Ref.modify_ (\s -> s { subscribers = Array.filter (_ /= callback) s.subscribers }) stateRef
    }

-- | Create a computed signal
computed :: forall a b. Signal a -> (a -> b) -> Effect (Signal b)
computed source f = do
  initialValue <- source.get
  let initialComputed = f initialValue
  computedSignal <- create initialComputed
  
  -- Subscribe to source and update computed
  unsubscribe <- source.subscribe \newValue -> do
    let computedValue = f newValue
    computedSignal.set computedValue
  
  -- Return computed signal (unsubscribe would be called when signal is disposed)
  pure computedSignal
