-- | Deferred execution utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/util/defer.ts
module Forge.Util.Defer where

import Prelude
import Effect.Aff (Aff)
import Forge.Util.NotImplemented (notImplemented)

-- | Deferred value
type Deferred a =
  { resolve :: a -> Aff Unit
  , reject :: String -> Aff Unit
  , promise :: Aff a
  }

-- | Create a deferred value
create :: forall a. Aff (Deferred a)
create = notImplemented "Util.Defer.create"
