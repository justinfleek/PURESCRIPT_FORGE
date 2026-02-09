-- | Main Server module
-- |
-- | HTTP server using Hono with routes for all Forge APIs.
-- | Includes CORS, basic auth, SSE events, and mDNS discovery.
-- |
-- | 1:1 parity with opencode-dev/packages/opencode/src/server/server.ts
module Forge.Server.Server
  ( url
  , app
  , openapi
  , listen
  , ListenOptions
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | Listen options
type ListenOptions =
  { port :: Int
  , hostname :: String
  , mdns :: Maybe Boolean
  , cors :: Maybe (Array String)
  }

-- | Get the current server URL
foreign import url :: Effect Foreign  -- URL

-- | Get the Hono app instance (lazily initialized)
foreign import app :: Effect Foreign  -- Hono

-- | Generate OpenAPI spec from routes
foreign import openapi :: Aff Foreign  -- OpenAPI spec object

-- | Start the server listening
-- | Returns a Bun server instance
foreign import listen :: ListenOptions -> Effect Foreign  -- Bun.Server
