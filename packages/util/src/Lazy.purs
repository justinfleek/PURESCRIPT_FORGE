-- | Lazy evaluation with memoization
-- | Migrated from forge-dev/packages/util/src/lazy.ts
module Forge.Util.Lazy
  ( Lazy
  , lazy
  , force
  ) where

import Prelude
import Effect (Effect)
import Effect.Ref (Ref, new, read, write)
import Data.Maybe (Maybe(..))

-- | A lazily evaluated value
newtype Lazy a = Lazy (Ref (LazyState a))

data LazyState a
  = NotComputed (Effect a)
  | Computed a

-- | Create a lazy value
lazy :: forall a. Effect a -> Effect (Lazy a)
lazy thunk = do
  ref <- new (NotComputed thunk)
  pure (Lazy ref)

-- | Force evaluation of a lazy value
force :: forall a. Lazy a -> Effect a
force (Lazy ref) = do
  state <- read ref
  case state of
    Computed value -> pure value
    NotComputed thunk -> do
      value <- thunk
      write (Computed value) ref
      pure value
