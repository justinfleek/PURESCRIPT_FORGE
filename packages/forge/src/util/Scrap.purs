-- | Scrap utilities (test/scratch data)
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/scrap.ts
module Forge.Util.Scrap
  ( foo
  , bar
  , dummyFunction
  , randomHelper
  ) where

import Prelude
import Effect (Effect)

-- | Test constant string
foreign import foo :: String

-- | Test constant number
foreign import bar :: Int

-- | Dummy function for testing
foreign import dummyFunction :: Effect Unit

-- | Random helper for testing
foreign import randomHelper :: Effect Boolean
