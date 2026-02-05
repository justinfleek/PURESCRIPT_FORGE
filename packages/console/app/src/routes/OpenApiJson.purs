-- | OpenAPI JSON Route Handler
-- |
-- | Fetches and returns OpenAPI spec from GitHub.
-- | PureScript wrapper around SolidJS Start route handler.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/openapi.json.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.OpenApiJson
  ( handleOpenApiGET
  ) where

import Prelude

import Effect.Aff (Aff)
import Foreign (Foreign)
import Console.App.FFI.SolidStart (APIEvent, jsonResponse)

-- | OpenAPI spec URL
openApiUrl :: String
openApiUrl = "https://raw.githubusercontent.com/anomalyco/opencode/refs/heads/dev/packages/sdk/openapi.json"

-- | FFI: Fetch JSON from URL
foreign import fetchJson :: String -> Aff Foreign

-- | Handle GET request - fetch and return OpenAPI spec
handleOpenApiGET :: APIEvent -> Aff Response
handleOpenApiGET _event = do
  json <- fetchJson openApiUrl
  jsonResponse (toJsonString json)

-- | FFI: Convert to JSON string
foreign import toJsonString :: Foreign -> String
