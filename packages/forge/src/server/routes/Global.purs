-- | Global route
-- | 1:1 parity with opencode-dev/packages/opencode/src/server/routes/global.ts
module Forge.Server.Routes.Global where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Foreign (Foreign)

-- | Get global configuration and paths
get :: Aff (Either String Foreign)
get = getFFI

-- | Get environment info
env :: Aff (Either String Foreign)
env = envFFI

foreign import getFFI :: Aff (Either String Foreign)
foreign import envFFI :: Aff (Either String Foreign)
