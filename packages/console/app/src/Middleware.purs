-- | Application Middleware
-- |
-- | SolidJS Start middleware configuration.
-- | Currently empty middleware (onBeforeResponse hook is no-op).
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/middleware.ts
-- | Migrated: 2026-02-04
module Console.App.Middleware
  ( createMiddleware
  , Middleware
  ) where

import Prelude

import Effect (Effect)

-- | Middleware type (opaque)
foreign import data Middleware :: Type

-- | FFI: Create SolidJS Start middleware
-- | Creates middleware with empty onBeforeResponse hook
foreign import createMiddleware :: Effect Middleware
