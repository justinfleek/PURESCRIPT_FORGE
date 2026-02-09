-- | Event loop utilities
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/eventloop.ts
module Forge.Util.EventLoop
  ( wait
  ) where

import Prelude
import Effect.Aff (Aff)

-- | Wait for event loop to drain (no active handles/requests)
foreign import wait :: Aff Unit
