-- | SDK context - manages Forge client SDK
-- | Migrated from: forge-dev/packages/app/src/context/sdk.tsx
module App.Context.SDK
  ( SDKContext
  , mkSDKContext
  , getDirectory
  , getUrl
  ) where

import Prelude

import Effect.Aff (Aff)

-- | SDK context
type SDKContext =
  { directory :: String
  , url :: String
  }

-- | Create SDK context
mkSDKContext :: String -> String -> SDKContext
mkSDKContext directory url =
  { directory, url }

-- | Get directory
getDirectory :: SDKContext -> String
getDirectory = _.directory

-- | Get URL
getUrl :: SDKContext -> String
getUrl = _.url
