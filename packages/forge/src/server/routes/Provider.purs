-- | Provider route
-- | 1:1 parity with opencode-dev/packages/opencode/src/server/routes/provider.ts
module Forge.Server.Routes.Provider where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | List all providers
list :: Aff (Either String (Array Foreign))
list = listFFI

-- | Get a specific provider
get :: String -> Aff (Either String (Maybe Foreign))
get providerID = getFFI providerID

-- | Get models for a provider
models :: String -> Aff (Either String (Array Foreign))
models providerID = modelsFFI providerID

foreign import listFFI :: Aff (Either String (Array Foreign))
foreign import getFFI :: String -> Aff (Either String (Maybe Foreign))
foreign import modelsFFI :: String -> Aff (Either String (Array Foreign))
