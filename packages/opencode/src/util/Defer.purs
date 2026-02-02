-- | Deferred execution utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/util/defer.ts
module Opencode.Util.Defer where

import Prelude
import Effect.Aff (Aff)
import Opencode.Util.NotImplemented (notImplemented)

-- | Deferred value
type Deferred a =
  { resolve :: a -> Aff Unit
  , reject :: String -> Aff Unit
  , promise :: Aff a
  }

-- | Create a deferred value
create :: forall a. Aff (Deferred a)
create = notImplemented "Util.Defer.create"
