-- | Validated function wrapper
-- | Migrated from forge-dev/packages/util/src/fn.ts
module Forge.Util.Fn
  ( ValidatedFn
  , fn
  , force
  ) where

import Prelude
import Data.Either (Either(..))

-- | A function with validation
type ValidatedFn e a b = 
  { run :: a -> Either e b
  , force :: a -> b
  }

-- | Create a validated function
fn :: forall e a b. (a -> Either e a) -> (a -> b) -> ValidatedFn e a b
fn validate cb =
  { run: \input -> case validate input of
      Left err -> Left err
      Right validated -> Right (cb validated)
  , force: cb
  }

-- | Run without validation (use with caution)
force :: forall e a b. ValidatedFn e a b -> a -> b
force vfn = vfn.force
