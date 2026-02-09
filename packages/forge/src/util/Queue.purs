-- | Queue utilities (async queue and work processing)
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/queue.ts
module Forge.Util.Queue
  ( AsyncQueue
  , createQueue
  , push
  , next
  , work
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Foreign (Foreign)

-- | Async queue type (opaque)
foreign import data AsyncQueue :: Type -> Type

-- | Create a new async queue
foreign import createQueue :: forall a. Effect (AsyncQueue a)

-- | Push an item to the queue
foreign import push :: forall a. AsyncQueue a -> a -> Effect Unit

-- | Get next item from queue (blocks if empty)
foreign import next :: forall a. AsyncQueue a -> Aff a

-- | Process items with concurrency limit
foreign import work :: forall a. Int -> Array a -> (a -> Aff Unit) -> Aff Unit
