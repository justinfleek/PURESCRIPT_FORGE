-- | Provider Authentication
module Opencode.Provider.Auth where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Map as Map
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- | Provider authentication info
type ProviderAuth =
  { provider :: String
  , apiKey :: Maybe String
  , token :: Maybe String
  , expiresAt :: Maybe Number
  }

-- | In-memory auth storage (in production, would use persistent storage)
authStorageRef :: Ref (Map.Map String ProviderAuth)
authStorageRef = unsafePerformEffect $ Ref.new Map.empty
  where
    foreign import unsafePerformEffect :: forall a. Effect a -> a

-- | Get authentication for a provider
getAuth :: String -> Aff (Either String ProviderAuth)
getAuth provider = do
  storage <- liftEffect $ Ref.read authStorageRef
  case Map.lookup provider storage of
    Nothing -> pure $ Left ("Provider not authenticated: " <> provider)
    Just auth -> pure $ Right auth

-- | Set authentication for a provider
setAuth :: String -> ProviderAuth -> Aff (Either String Unit)
setAuth provider auth = do
  liftEffect $ Ref.modify_ (\storage -> Map.insert provider auth storage) authStorageRef
  pure $ Right unit

-- | Clear authentication for a provider
clearAuth :: String -> Aff (Either String Unit)
clearAuth provider = do
  liftEffect $ Ref.modify_ (\storage -> Map.delete provider storage) authStorageRef
  pure $ Right unit

-- | Check if provider is authenticated
isAuthenticated :: String -> Aff Boolean
isAuthenticated provider = do
  result <- getAuth provider
  pure $ case result of
    Left _ -> false
    Right auth -> isJust auth.token || isJust auth.apiKey

import Effect (Effect)
