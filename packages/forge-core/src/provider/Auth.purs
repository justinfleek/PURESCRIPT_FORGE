-- | Provider Authentication
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/provider/auth.ts
module Forge.Provider.Auth where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Provider authentication info
type ProviderAuth =
  { provider :: String
  , apiKey :: Maybe String
  , token :: Maybe String
  , expiresAt :: Maybe Number
  }

-- | Get authentication for a provider
getAuth :: String -> Aff (Either String ProviderAuth)
getAuth provider = notImplemented "Provider.Auth.getAuth"

-- | Set authentication for a provider
setAuth :: String -> ProviderAuth -> Aff (Either String Unit)
setAuth provider auth = notImplemented "Provider.Auth.setAuth"

-- | Clear authentication for a provider
clearAuth :: String -> Aff (Either String Unit)
clearAuth provider = notImplemented "Provider.Auth.clearAuth"

-- | Check if provider is authenticated
isAuthenticated :: String -> Aff Boolean
isAuthenticated provider = notImplemented "Provider.Auth.isAuthenticated"
