-- | Timeout utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/util/timeout.ts
module Opencode.Util.Timeout where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Run with timeout
withTimeout :: forall a. Int -> Aff a -> Aff (Either String a)
withTimeout ms action = notImplemented "Util.Timeout.withTimeout"

-- | Delay execution
delay :: Int -> Aff Unit
delay ms = notImplemented "Util.Timeout.delay"

-- | Create a timeout error
timeoutError :: String
timeoutError = "Operation timed out"
