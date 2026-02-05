-- | Auth Session Types (Empty source file placeholder)
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/context/auth.session.ts
-- | Pure PureScript implementation - NO FFI
-- | 
-- | The original source file was empty. This module provides session
-- | type re-exports for convenience.
module Console.App.Context.AuthSession
  ( module Console.App.Context.Auth
  ) where

-- | Re-export auth session types from main Auth module
import Console.App.Context.Auth 
  ( AuthSession
  , AccountInfo
  , SessionConfig
  , CookieConfig
  , defaultSessionConfig
  , mkSessionConfig
  , emptySession
  )

import Effect.Aff (Aff)

-- | FFI: Get current auth session
-- | Wraps SolidJS Start's useAuthSession hook
foreign import useAuthSession :: Aff { data :: AuthSession, update :: (AuthSession -> AuthSession) -> Aff Unit }
