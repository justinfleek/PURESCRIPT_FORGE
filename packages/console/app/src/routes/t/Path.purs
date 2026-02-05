-- | Enterprise Proxy Route
-- | Proxies requests to enterprise.opencode.ai
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/t/[...path].tsx
-- | Migrated: 2026-02-04
module Console.App.Routes.T.Path
  ( handleEnterpriseProxy
  ) where

import Prelude

import Effect.Aff (Aff)
import Console.App.FFI.SolidStart (APIEvent, Response)

-- | Handle enterprise proxy request
handleEnterpriseProxy :: APIEvent -> Aff Response
handleEnterpriseProxy event = proxyRequest event

-- | Proxy request to enterprise.opencode.ai (FFI boundary)
foreign import proxyRequest :: APIEvent -> Aff Response
