-- | Immediately invoked function expression
-- | Migrated from opencode-dev/packages/util/src/iife.ts
module Opencode.Util.Iife
  ( iife
  ) where

import Prelude

-- | Execute a thunk immediately and return the result
iife :: forall a. (Unit -> a) -> a
iife f = f unit
