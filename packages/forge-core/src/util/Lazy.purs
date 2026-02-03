-- | Lazy evaluation utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/util/lazy.ts
module Forge.Util.Lazy where

import Prelude
import Effect (Effect)
import Forge.Util.NotImplemented (notImplemented)

-- | Lazy value type
type Lazy a =
  { get :: Effect a
  }

-- | Create a lazy value
lazy :: forall a. (Unit -> a) -> Lazy a
lazy f = { get: notImplemented "Util.Lazy.lazy" }

-- | Force evaluation of lazy value
force :: forall a. Lazy a -> Effect a
force l = l.get
