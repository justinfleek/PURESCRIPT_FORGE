-- | Session Management - User Session Lifecycle and State
-- |
-- | Manages user sessions, including creation, validation, expiration,
-- | refresh, and invalidation. Tracks session state and metadata.
module Bridge.Auth.Session where

import Prelude

import Data.Either (Either)
import Data.Maybe (Maybe)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Bridge.FFI.Haskell.Database as DB

-- | Session data
type Session =
  { id :: String
  , userId :: String
  , accessToken :: String
  , refreshToken :: String
  , createdAt :: Number
  , expiresAt :: Number
  , refreshExpiresAt :: Number
  , lastActivityAt :: Number
  , ipAddress :: String
  , userAgent :: String
  , isActive :: Boolean
  }

-- | Session creation options
type CreateSessionOptions =
  { userId :: String
  , ipAddress :: String
  , userAgent :: String
  , expiresIn :: Maybe Int
  , refreshExpiresIn :: Maybe Int
  }

-- | Session validation result
type SessionValidationResult =
  { valid :: Boolean
  , session :: Maybe Session
  , error :: Maybe String
  }

-- FFI declarations (top-level)
foreign import createSessionImpl :: CreateSessionOptions -> DB.Database -> EffectFnAff (Either String Session)
foreign import validateSessionImpl :: String -> DB.Database -> EffectFnAff (Either String Session)
foreign import refreshSessionImpl :: String -> DB.Database -> EffectFnAff (Either String Session)
foreign import invalidateSessionImpl :: String -> DB.Database -> EffectFnAff (Either String Unit)
foreign import updateSessionActivityImpl :: String -> DB.Database -> EffectFnAff (Either String Unit)
foreign import getUserSessionsImpl :: String -> DB.Database -> EffectFnAff (Array Session)
foreign import cleanupExpiredSessionsImpl :: DB.Database -> EffectFnAff Int

-- | Create new session
createSession :: CreateSessionOptions -> DB.Database -> Aff (Either String Session)
createSession options db =
  fromEffectFnAff $ createSessionImpl options db

-- | Validate session
validateSession :: String -> DB.Database -> Aff (Either String Session)
validateSession sessionId db =
  fromEffectFnAff $ validateSessionImpl sessionId db

-- | Refresh session using refresh token
refreshSession :: String -> DB.Database -> Aff (Either String Session)
refreshSession refreshToken db =
  fromEffectFnAff $ refreshSessionImpl refreshToken db

-- | Invalidate session immediately
invalidateSession :: String -> DB.Database -> Aff (Either String Unit)
invalidateSession sessionId db =
  fromEffectFnAff $ invalidateSessionImpl sessionId db

-- | Update session activity timestamp
updateSessionActivity :: String -> DB.Database -> Aff (Either String Unit)
updateSessionActivity sessionId db =
  fromEffectFnAff $ updateSessionActivityImpl sessionId db

-- | Get all active sessions for user
getUserSessions :: String -> DB.Database -> Aff (Array Session)
getUserSessions userId db =
  fromEffectFnAff $ getUserSessionsImpl userId db

-- | Cleanup expired sessions
cleanupExpiredSessions :: DB.Database -> Aff Int
cleanupExpiredSessions db =
  fromEffectFnAff $ cleanupExpiredSessionsImpl db
