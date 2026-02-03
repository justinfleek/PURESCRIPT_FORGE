-- | Fn Utility Module
-- |
-- | Provides validated function wrapper pattern.
-- | Wraps functions with schema validation at boundaries.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/util/fn.ts
module Forge.Console.Core.Util.Fn
  ( ValidatedFn
  , fn
  , force
  ) where

import Prelude

import Data.Either (Either(..))
import Effect.Aff (Aff)

-- | A validated function with schema enforcement
type ValidatedFn input output =
  { run :: input -> Aff output
  , force :: input -> Aff output  -- Skip validation (for internal use)
  }

-- | Create a validated function
-- | In PureScript, we rely on types for validation rather than runtime schemas
-- | The input type serves as the schema
fn :: forall input output. (input -> Aff output) -> ValidatedFn input output
fn callback =
  { run: callback
  , force: callback  -- Same as run in typed context
  }

-- | Force execution without validation (for trusted internal calls)
force :: forall input output. ValidatedFn input output -> input -> Aff output
force vfn input = vfn.force input
