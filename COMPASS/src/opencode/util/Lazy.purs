-- | Lazy evaluation utilities
module Opencode.Util.Lazy where

import Prelude
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Data.Maybe (Maybe(..))

-- | Lazy value type
type Lazy a =
  { get :: Effect a
  }

-- | Internal lazy state
type LazyState a =
  { thunk :: Unit -> a
  , cached :: Maybe a
  }

-- | Create a lazy value
lazy :: forall a. (Unit -> a) -> Lazy a
lazy thunk = 
  let stateRef = unsafePerformEffect $ Ref.new { thunk, cached: Nothing }
  in
    { get: do
        state <- Ref.read stateRef
        case state.cached of
          Just value -> pure value
          Nothing -> do
            let value = state.thunk unit
            Ref.write { thunk: state.thunk, cached: Just value } stateRef
            pure value
    }
  where
    foreign import unsafePerformEffect :: forall a. Effect a -> a

-- | Force evaluation of lazy value
force :: forall a. Lazy a -> Effect a
force l = l.get
