-- | Deferred execution utilities
module Opencode.Util.Defer where

import Prelude
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Aff as Aff
import Data.Either (Either(..))

-- | Deferred value
type Deferred a =
  { resolve :: a -> Aff Unit
  , reject :: String -> Aff Unit
  , promise :: Aff a
  }

-- | Create a deferred value
create :: forall a. Aff (Deferred a)
create = do
  -- Create a promise that can be resolved/rejected externally
  resolverRef <- liftEffect $ Aff.makeVar (Left $ Aff.error "Deferred not resolved")
  
  let resolve value = do
        liftEffect $ Aff.putVar resolverRef (Right value)
        pure unit
      
      reject err = do
        liftEffect $ Aff.putVar resolverRef (Left $ Aff.error err)
        pure unit
      
      promise = do
        result <- liftEffect $ Aff.takeVar resolverRef
        case result of
          Right value -> pure value
          Left error -> Aff.throwError error
  
  pure { resolve, reject, promise }
