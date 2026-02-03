-- | Immediately invoked function expression
-- | Migrated from forge-dev/packages/util/src/iife.ts
module Forge.Util.Iife
  ( iife
  ) where

import Prelude

-- | Execute a thunk immediately and return the result
iife :: forall a. (Unit -> a) -> a
iife f = f unit
