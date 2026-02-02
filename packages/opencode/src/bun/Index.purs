-- | Bun runtime utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/bun/index.ts
-- | Note: This will be replaced by native PureScript/Haskell implementations
module Opencode.Bun.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Check if running in Bun
isBun :: Boolean
isBun = false -- We're running in PureScript, not Bun

-- | Get Bun version (N/A for PureScript)
version :: String
version = "N/A"
