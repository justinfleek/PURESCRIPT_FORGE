-- | Auth Status Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/auth/status.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Auth.Status
  ( StatusResponse(..)
  , handleStatus
  ) where

import Prelude

import Console.App.Context.Auth (AuthSession)

-- | Status response type
type StatusResponse =
  { session :: AuthSession
  }

-- | Handle status request (pure)
-- | Returns the current session data as JSON
handleStatus :: AuthSession -> StatusResponse
handleStatus session = { session }

-- | Build JSON response (pure data)
type JsonResponse a =
  { data :: a
  , contentType :: String
  }

-- | Create JSON response
jsonResponse :: forall a. a -> JsonResponse a
jsonResponse d = { data: d, contentType: "application/json" }
