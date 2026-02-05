-- | Session Proxy Route
-- | Proxies requests to docs.opencode.ai/docs with session path
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/s/[id].ts
-- | Migrated: 2026-02-04
module Console.App.Routes.S.Id
  ( handleSessionProxy
  , buildSessionUrl
  ) where

import Prelude

import Effect.Aff (Aff)
import Console.App.FFI.SolidStart (APIEvent, Response)

-- | Docs base URL with session path prefix
docsBaseUrl :: String
docsBaseUrl = "https://docs.opencode.ai/docs"

-- | Build proxy URL from request
buildSessionUrl :: String -> String -> String -> String
buildSessionUrl sessionId pathname search =
  docsBaseUrl <> "/" <> sessionId <> pathname <> search

-- | Handle session proxy request (FFI boundary)
-- | Proxies all HTTP methods to docs.opencode.ai/docs/{sessionId}...
foreign import handleSessionProxy :: APIEvent -> String -> Aff Response
