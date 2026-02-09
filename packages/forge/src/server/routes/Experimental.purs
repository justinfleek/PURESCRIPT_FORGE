-- | Experimental routes
-- | 1:1 parity with opencode-dev/packages/opencode/src/server/routes/experimental.ts
module Forge.Server.Routes.Experimental where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Foreign (Foreign)

-- | Execute experimental endpoint
experimental :: String -> Aff (Either String Foreign)
experimental endpoint = experimentalFFI endpoint

-- | List experimental features
listFeatures :: Aff (Either String (Array Foreign))
listFeatures = listFeaturesFFI

-- | Enable experimental feature
enableFeature :: String -> Aff (Either String Unit)
enableFeature featureID = enableFeatureFFI featureID

-- | Disable experimental feature
disableFeature :: String -> Aff (Either String Unit)
disableFeature featureID = disableFeatureFFI featureID

foreign import experimentalFFI :: String -> Aff (Either String Foreign)
foreign import listFeaturesFFI :: Aff (Either String (Array Foreign))
foreign import enableFeatureFFI :: String -> Aff (Either String Unit)
foreign import disableFeatureFFI :: String -> Aff (Either String Unit)
