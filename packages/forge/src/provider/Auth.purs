-- | Provider Authentication
-- |
-- | Handles OAuth and API key authentication for providers.
-- |
-- | 1:1 parity with opencode-dev/packages/opencode/src/provider/auth.ts
module Forge.Provider.Auth
  ( Method
  , Authorization
  , AuthorizeInput
  , CallbackInput
  , ApiInput
  , methods
  , authorize
  , callback
  , api
  , oauthMissing
  , oauthCodeMissing
  , oauthCallbackFailed
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Foreign (Foreign)
import Foreign.Object (Object)

-- | Auth method type
type Method =
  { "type" :: String  -- "oauth" | "api"
  , label :: String
  }

-- | Authorization response for OAuth
type Authorization =
  { url :: String
  , method :: String  -- "auto" | "code"
  , instructions :: String
  }

-- | Input for authorize
type AuthorizeInput =
  { providerID :: String
  , method :: Int
  }

-- | Input for callback
type CallbackInput =
  { providerID :: String
  , method :: Int
  , code :: Maybe String
  }

-- | Input for API key auth
type ApiInput =
  { providerID :: String
  , key :: String
  }

-- | Get available auth methods for all providers
-- | Returns a map of providerID -> array of methods
foreign import methods :: Aff (Object (Array Method))

-- | Start OAuth authorization flow
-- | Returns authorization URL and instructions
foreign import authorize :: AuthorizeInput -> Aff (Maybe Authorization)

-- | Complete OAuth callback
-- | Stores credentials on success
foreign import callback :: CallbackInput -> Aff Unit

-- | Set API key authentication
foreign import api :: ApiInput -> Aff Unit

-- | Error types
foreign import oauthMissing :: Foreign
foreign import oauthCodeMissing :: Foreign
foreign import oauthCallbackFailed :: Foreign
