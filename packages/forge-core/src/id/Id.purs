-- | ID Generation
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/id/id.ts
module Forge.Id.Id where

import Prelude
import Effect (Effect)
import Forge.Util.NotImplemented (notImplemented)

-- | Generate a unique ID
generate :: Effect String
generate = notImplemented "Id.Id.generate"

-- | Generate a short ID
generateShort :: Effect String
generateShort = notImplemented "Id.Id.generateShort"

-- | Validate an ID
isValid :: String -> Boolean
isValid id = true -- TODO: Implement validation
