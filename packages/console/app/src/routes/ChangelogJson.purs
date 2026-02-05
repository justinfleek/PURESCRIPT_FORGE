-- | Changelog JSON Route Handler
-- |
-- | Returns changelog data as JSON with CORS headers.
-- | PureScript wrapper around SolidJS Start route handler.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/changelog.json.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.ChangelogJson
  ( handleChangelogGET
  , handleChangelogOPTIONS
  ) where

import Prelude

import Effect.Aff (Aff)
import Console.App.FFI.SolidStart (APIEvent, jsonResponse, textResponse)
import Console.App.Lib.Changelog (loadChangelog)

-- | CORS headers
corsHeaders :: { origin :: String, methods :: String, headers :: String }
corsHeaders =
  { origin: "*"
  , methods: "GET, OPTIONS"
  , headers: "Content-Type, Authorization"
  }

-- | Cache control for successful response
okCacheControl :: String
okCacheControl = "public, max-age=1, s-maxage=300, stale-while-revalidate=86400, stale-if-error=86400"

-- | Cache control for error response
errorCacheControl :: String
errorCacheControl = "public, max-age=1, s-maxage=60, stale-while-revalidate=600, stale-if-error=86400"

-- | Handle GET request - return changelog JSON
handleChangelogGET :: APIEvent -> Aff Response
handleChangelogGET _event = do
  result <- loadChangelog
  case result.ok of
    true -> jsonResponse (toJsonString { releases: result.releases })
    false -> textResponse (toJsonString { releases: [] }) 503

-- | Handle OPTIONS request - CORS preflight
handleChangelogOPTIONS :: APIEvent -> Aff Response
handleChangelogOPTIONS _event = textResponse "" 200

-- | FFI: Convert releases to JSON string
foreign import toJsonString :: { releases :: Array ChangelogRelease } -> String
