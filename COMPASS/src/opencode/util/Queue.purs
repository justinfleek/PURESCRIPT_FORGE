-- | Queue utilities
module Opencode.Util.Queue where

import Prelude
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Control.Monad.Rec.Class (forever)
import Effect.Aff as Aff

-- | Queue type
type Queue a =
  { enqueue :: a -> Aff Unit
  , dequeue :: Aff (Maybe a)
  , size :: Aff Int
  , isEmpty :: Aff Boolean
  }

-- | Internal queue state
type QueueState a =
  { items :: Array a
  , maxSize :: Maybe Int
  , waiters :: Array (a -> Effect Unit)
  }

-- | Create a new queue
create :: forall a. Aff (Queue a)
create = do
  stateRef <- liftEffect $ Ref.new { items: [], maxSize: Nothing, waiters: [] }
  pure $ mkQueue stateRef

-- | Create a bounded queue
createBounded :: forall a. Int -> Aff (Queue a)
createBounded maxSize = do
  stateRef <- liftEffect $ Ref.new { items: [], maxSize: Just maxSize, waiters: [] }
  pure $ mkQueue stateRef

-- | Create queue interface from state ref
mkQueue :: forall a. Ref (QueueState a) -> Queue a
mkQueue stateRef =
  let enqueueFn item = do
        state <- liftEffect $ Ref.read stateRef
        case state.maxSize of
          Just max -> do
            if Array.length state.items >= max
              then do
                -- Wait for space (simplified - would use proper async waiting)
                liftAff $ Aff.delay (Aff.Milliseconds 10.0)
                enqueueFn item
              else do
                liftEffect $ Ref.modify_ (\s -> s { items = Array.snoc s.items item }) stateRef
          Nothing -> do
            liftEffect $ Ref.modify_ (\s -> s { items = Array.snoc s.items item }) stateRef
  in
    { enqueue: enqueueFn
    , dequeue: do
        state <- liftEffect $ Ref.read stateRef
        case Array.uncons state.items of
          Nothing -> pure Nothing
          Just { head, tail } -> do
            liftEffect $ Ref.modify_ (\s -> s { items = tail }) stateRef
            pure $ Just head
    , size: do
        state <- liftEffect $ Ref.read stateRef
        pure $ Array.length state.items
    , isEmpty: do
        state <- liftEffect $ Ref.read stateRef
        pure $ Array.null state.items
    }
