-- | NotImplemented utility for runtime error reporting
module Forge.Util.NotImplemented 
  ( notImplemented
  , notImplementedEffect
  , notImplementedAff
  ) where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Exception (throw)
import Effect.Class (class MonadEffect, liftEffect)

-- | Throw a not implemented error with a function name
-- | This version works in any MonadEffect context (Effect, Aff, etc.)
-- | 
-- | Usage:
-- | ```purescript
-- | myFunction :: Aff (Either String Int)
-- | myFunction = notImplemented "myFunction"
-- | ```
notImplemented :: forall m a. MonadEffect m => String -> m a
notImplemented fnName = liftEffect $ throw $ "Not implemented: " <> fnName

-- | Effect-specific version (for when you need explicit Effect)
notImplementedEffect :: forall a. String -> Effect a
notImplementedEffect fnName = throw $ "Not implemented: " <> fnName

-- | Aff-specific version (for when you need explicit Aff)
notImplementedAff :: forall a. String -> Aff a
notImplementedAff fnName = liftEffect $ throw $ "Not implemented: " <> fnName
