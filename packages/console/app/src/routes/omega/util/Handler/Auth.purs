-- | Omega Handler Authentication
-- | Authentication logic with DB operations as FFI boundary
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/handler.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Handler.Auth
  ( authenticate
  , AuthData
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array (elem)
import Console.App.Routes.Omega.Util.Error (OmegaError(..), AuthError)
import Console.App.Routes.Omega.Util.Handler.Types (AuthInfo, ModelInfo, Date)
import Console.Core.Identifier (WorkspaceId, UserId)
import Console.Core.Util.Price (MicroCents)

-- | Free workspaces that don't require billing
freeWorkspaces :: Array String
freeWorkspaces =
  [ "wrk_01K46JDFR0E75SG2Q8K172KF3Y"  -- frank
  , "wrk_01K6W1A3VE0KMNVSCQT43BG2SX"  -- opencode bench
  ]

-- | Authentication data from database
type AuthData =
  { apiKey :: String
  , workspaceID :: WorkspaceId
  , billing ::
      { balance :: MicroCents
      , paymentMethodID :: Maybe String
      , monthlyLimit :: Maybe Int  -- dollars
      , monthlyUsage :: Maybe MicroCents
      , timeMonthlyUsageUpdated :: Maybe Date
      , reloadTrigger :: Maybe Int  -- dollars
      , timeReloadLockedTill :: Maybe Date
      , subscription :: Maybe
          { plan :: String
          , useBalance :: Boolean
          }
      }
  , user ::
      { id :: UserId
      , monthlyLimit :: Maybe Int  -- dollars
      , monthlyUsage :: Maybe MicroCents
      , timeMonthlyUsageUpdated :: Maybe Date
      }
  , subscription :: Maybe
      { id :: String
      , rollingUsage :: Maybe MicroCents
      , fixedUsage :: Maybe MicroCents
      , timeRollingUpdated :: Maybe Date
      , timeFixedUpdated :: Maybe Date
      }
  , provider :: Maybe
      { credentials :: String
      }
  , timeDisabled :: Maybe Date
  }

-- | Authenticate API key and return auth info
authenticate ::
  ModelInfo ->
  String ->  -- apiKey
  Aff (Either OmegaError AuthInfo)
authenticate modelInfo apiKey = do
  -- Parse API key
  if apiKey == "" || apiKey == "public"
    then
      if modelInfo.allowAnonymous
        then pure $ Right anonymousAuthInfo
        else pure $ Left $ AuthError "Missing API key."
    else do
      -- Query database for API key (FFI boundary - converts to PureScript types)
      authData <- queryAuthData apiKey modelInfo.id modelInfo.byokProvider
      case authData of
        Nothing -> pure $ Left $ AuthError "Invalid API key."
        Just data -> pure $ Right $ buildAuthInfo data

-- | Anonymous auth info
anonymousAuthInfo :: AuthInfo
anonymousAuthInfo =
  { apiKeyId: ""
  , workspaceID: ""
  , billing:
      { balance: 0
      , paymentMethodID: Nothing
      , monthlyLimit: Nothing
      , monthlyUsage: Nothing
      , timeMonthlyUsageUpdated: Nothing
      , reloadTrigger: Nothing
      , timeReloadLockedTill: Nothing
      , subscription: Nothing
      }
  , user:
      { id: ""
      , monthlyLimit: Nothing
      , monthlyUsage: Nothing
      , timeMonthlyUsageUpdated: Nothing
      }
  , subscription: Nothing
  , provider: Nothing
  , isFree: false
  , isDisabled: false
  }

-- | Build auth info from database data
buildAuthInfo :: AuthData -> AuthInfo
buildAuthInfo data =
  { apiKeyId: data.apiKey
  , workspaceID: data.workspaceID
  , billing: data.billing
  , user: data.user
  , subscription: data.subscription
  , provider: data.provider
  , isFree: isFreeWorkspace data.workspaceID
  , isDisabled: isJust data.timeDisabled
  }

-- | Check if workspace is free
isFreeWorkspace :: WorkspaceId -> Boolean
isFreeWorkspace workspaceID =
  elem workspaceID freeWorkspaces

-- | Query authentication data from database (FFI boundary)
-- | FFI converts from JavaScript to PureScript types immediately
foreign import queryAuthData ::
  String ->  -- apiKey
  String ->  -- modelId
  Maybe String ->  -- byokProvider (pure PureScript type)
  Aff (Maybe AuthData)
