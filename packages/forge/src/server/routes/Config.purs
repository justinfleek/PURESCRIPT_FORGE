-- | Config route
-- | 1:1 parity with opencode-dev/packages/opencode/src/server/routes/config.ts
module Forge.Server.Routes.Config where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Foreign (Foreign)

-- | Get current config
get :: Aff (Either String Foreign)
get = getFFI

-- | Update config
update :: Foreign -> Aff (Either String Unit)
update updates = updateFFI updates

-- | Set specific config key
set :: String -> Foreign -> Aff (Either String Unit)
set key value = setFFI key value

foreign import getFFI :: Aff (Either String Foreign)
foreign import updateFFI :: Foreign -> Aff (Either String Unit)
foreign import setFFI :: String -> Foreign -> Aff (Either String Unit)
