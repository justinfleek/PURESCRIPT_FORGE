-- | Docs Proxy Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/docs/index.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Docs.Index
  ( DocsProxyRequest(..)
  , DocsProxyResponse(..)
  , docsBaseUrl
  , buildProxyUrl
  , supportedMethods
  ) where

import Prelude

-- | Docs base URL
docsBaseUrl :: String
docsBaseUrl = "https://docs.opencode.ai"

-- | Proxy request configuration
type DocsProxyRequest =
  { method :: String
  , pathname :: String
  , search :: String
  , headers :: Array { name :: String, value :: String }
  }

-- | Proxy response
type DocsProxyResponse =
  { status :: Int
  , headers :: Array { name :: String, value :: String }
  }

-- | Build proxy target URL
buildProxyUrl :: String -> String -> String
buildProxyUrl pathname search = docsBaseUrl <> pathname <> search

-- | Supported HTTP methods for proxy
supportedMethods :: Array String
supportedMethods = ["GET", "POST", "PUT", "DELETE", "OPTIONS", "PATCH"]
