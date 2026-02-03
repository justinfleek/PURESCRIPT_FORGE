-- | Changelog JSON Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/changelog.json.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.ChangelogJson
  ( ChangelogJsonResponse(..)
  , CorsHeaders
  , CacheControl
  , corsHeaders
  , successCacheControl
  , errorCacheControl
  , handleGet
  , handleOptions
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Console.App.Lib.Changelog (ChangelogData, ChangelogRelease)

-- | CORS headers configuration
type CorsHeaders =
  { accessControlAllowOrigin :: String
  , accessControlAllowMethods :: String
  , accessControlAllowHeaders :: String
  }

-- | Default CORS headers
corsHeaders :: CorsHeaders
corsHeaders =
  { accessControlAllowOrigin: "*"
  , accessControlAllowMethods: "GET, OPTIONS"
  , accessControlAllowHeaders: "Content-Type, Authorization"
  }

-- | Cache control configuration
type CacheControl = String

-- | Success cache control (5 min server cache, long stale)
successCacheControl :: CacheControl
successCacheControl = 
  "public, max-age=1, s-maxage=300, stale-while-revalidate=86400, stale-if-error=86400"

-- | Error cache control (1 min server cache)
errorCacheControl :: CacheControl
errorCacheControl = 
  "public, max-age=1, s-maxage=60, stale-while-revalidate=600, stale-if-error=86400"

-- | JSON response configuration
type ChangelogJsonResponse =
  { status :: Int
  , contentType :: String
  , cacheControl :: CacheControl
  , body :: { releases :: Array ChangelogRelease }
  }

-- | Handle GET request (pure logic)
handleGet :: ChangelogData -> ChangelogJsonResponse
handleGet result =
  { status: if result.ok then 200 else 503
  , contentType: "application/json"
  , cacheControl: if result.ok then successCacheControl else errorCacheControl
  , body: { releases: result.releases }
  }

-- | OPTIONS response configuration
type OptionsResponse =
  { status :: Int
  , headers :: CorsHeaders
  }

-- | Handle OPTIONS request (pure)
handleOptions :: OptionsResponse
handleOptions =
  { status: 200
  , headers: corsHeaders
  }
