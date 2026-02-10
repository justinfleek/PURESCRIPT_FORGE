-- | Auth module - 1:1 parity with opencode-dev/src/auth/
-- | Re-exports all authentication and authorization modules
module Forge.Auth.Index
  ( module Bridge.Auth.JWT
  , module Bridge.Auth.Origin
  , module Bridge.Auth.RBAC
  , module Bridge.Auth.RateLimit
  , module Bridge.Auth.Session
  ) where

import Bridge.Auth.JWT (Claims, TokenOptions, generateToken, validateToken, decodeToken, getTokenExpiration)
import Bridge.Auth.Origin (AllowedOrigins, defaultAllowedOrigins, validateOrigin, extractOrigin, validateOriginFromRequest)
import Bridge.Auth.RBAC (Role(..), Permission, hasPermission, hasAnyPermission, hasAllPermissions, getEffectivePermissions, hasMinimumRole, authorize, AuthorizationResult)
import Bridge.Auth.RateLimit (RateLimitConfig, RateLimiter, RateLimitResult, createRateLimiter, checkRateLimit, resetRateLimit, getRateLimitStatus)
import Bridge.Auth.Session (Session, CreateSessionOptions, createSession, validateSession, refreshSession, invalidateSession, updateSessionActivity, getUserSessions, cleanupExpiredSessions)
