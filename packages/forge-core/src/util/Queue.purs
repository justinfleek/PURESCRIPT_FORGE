-- | Queue utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/util/queue.ts
module Forge.Util.Queue where

import Prelude
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Queue type
type Queue a =
  { enqueue :: a -> Aff Unit
  , dequeue :: Aff (Maybe a)
  , size :: Aff Int
  , isEmpty :: Aff Boolean
  }

-- | Create a new queue
create :: forall a. Aff (Queue a)
create = notImplemented "Util.Queue.create"

-- | Create a bounded queue
createBounded :: forall a. Int -> Aff (Queue a)
createBounded maxSize = notImplemented "Util.Queue.createBounded"
