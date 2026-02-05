-- | Session Status
module Opencode.Session.Status where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Map as Map

-- | Session status types
data SessionStatus
  = Active
  | Idle
  | Processing
  | WaitingForInput
  | Error String
  | Terminated

derive instance eqSessionStatus :: Eq SessionStatus

-- | Global status registry (in production, would use session state)
statusRegistryRef :: Ref (Map.Map String SessionStatus)
statusRegistryRef = unsafePerformEffect $ Ref.new Map.empty
  where
    foreign import unsafePerformEffect :: forall a. Effect a -> a

-- | Get session status
getStatus :: String -> Aff (Either String SessionStatus)
getStatus sessionId = do
  registry <- liftEffect $ Ref.read statusRegistryRef
  case Map.lookup sessionId registry of
    Nothing -> pure $ Right Idle  -- Default to Idle if not found
    Just status -> pure $ Right status

-- | Set session status
setStatus :: String -> SessionStatus -> Aff (Either String Unit)
setStatus sessionId status = do
  liftEffect $ Ref.modify_ (\registry -> Map.insert sessionId status registry) statusRegistryRef
  pure $ Right unit
