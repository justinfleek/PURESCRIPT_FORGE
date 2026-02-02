-- | Queue utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/util/queue.ts
module Opencode.Util.Queue where

import Prelude
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

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
