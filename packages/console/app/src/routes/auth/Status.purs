-- | Auth Status Route Handler
-- |
-- | Returns current auth session data as JSON.
-- | PureScript wrapper around SolidJS Start route handler.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/auth/status.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Auth.Status
  ( handleAuthStatus
  ) where

import Prelude

import Effect.Aff (Aff)
import Console.App.FFI.SolidStart (APIEvent, jsonResponse)
import Console.App.Context.Auth (AuthSession)
import Console.App.Context.AuthSession (useAuthSession)

-- | Handle auth status route
-- | Returns current session data as JSON
handleAuthStatus :: APIEvent -> Aff Response
handleAuthStatus _event = do
  session <- useAuthSession
  -- Convert session to JSON string (would use proper JSON encoding)
  let jsonStr = "{}"  -- Placeholder - would serialize session
  jsonResponse jsonStr
