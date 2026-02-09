-- | Token counting utilities
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/token.ts
module Forge.Util.Token
  ( estimate
  , charsPerToken
  ) where

import Prelude

-- | Characters per token estimate
foreign import charsPerToken :: Int

-- | Estimate token count for input string
foreign import estimate :: String -> Int
