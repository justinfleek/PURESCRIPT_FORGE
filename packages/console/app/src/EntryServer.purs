-- | Server Entry Point
-- |
-- | Creates SolidJS Start server handler with custom document template.
-- | PureScript wrapper around SolidJS Start's createHandler function.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/entry-server.tsx
-- | Migrated: 2026-02-04
module Console.App.EntryServer
  ( createServerHandler
  , ServerHandler
  , DocumentProps
  ) where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)

-- | Server handler type (opaque)
foreign import data ServerHandler :: Type

-- | Document props for server-side rendering
type DocumentProps =
  { assets :: String
  , children :: String
  , scripts :: String
  }

-- | Critical CSS for initial render
criticalCSS :: String
criticalCSS = "[data-component=\"top\"]{min-height:80px;display:flex;align-items:center}"

-- | FFI: Create SolidJS Start server handler
-- | Creates handler with custom document template and async mode
foreign import createServerHandler :: Effect ServerHandler
