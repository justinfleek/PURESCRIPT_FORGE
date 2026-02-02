-- | ID Generation
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/id/id.ts
module Opencode.Id.Id where

import Prelude
import Effect (Effect)
import Opencode.Util.NotImplemented (notImplemented)

-- | Generate a unique ID
generate :: Effect String
generate = notImplemented "Id.Id.generate"

-- | Generate a short ID
generateShort :: Effect String
generateShort = notImplemented "Id.Id.generateShort"

-- | Validate an ID
isValid :: String -> Boolean
isValid id = true -- TODO: Implement validation
