-- | Lazy evaluation utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/util/lazy.ts
module Opencode.Util.Lazy where

import Prelude
import Effect (Effect)
import Opencode.Util.NotImplemented (notImplemented)

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
