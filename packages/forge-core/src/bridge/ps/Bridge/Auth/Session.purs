-- | Session Management - User Session Lifecycle and State
-- |
-- | **What:** Manages user sessions, including creation, validation, expiration,
-- |         refresh, and invalidation. Tracks session state and metadata.
-- | **Why:** Provides secure session management with expiration, refresh tokens,
-- |         and invalidation capabilities. Enables tracking of active sessions
-- |         and session metadata (IP, user agent, last activity).
-- | **How:** Stores sessions in database with expiration timestamps. Provides
-- |         session refresh mechanism using refresh tokens. Tracks session activity
-- |         for security monitoring.
-- |
-- | **Dependencies:**
-- | - `Bridge.Auth.JWT`: JWT token generation/validation
-- | - `Bridge.FFI.Haskell.Database`: Session storage
-- | - `Bridge.FFI.Node.Pino`: Structured logging
-- |
-- | **Mathematical Foundation:**
-- | - **Session Invariant:** Each session has unique ID, user ID, creation time,
-- |   expiration time, and last activity time.
-- | - **Expiration:** Session expires when `now > expirationTime`
-- | - **Refresh:** Refresh token valid iff `now < refreshExpiration` and session active
-- |
-- | **Security Properties:**
-- | - Sessions expire after inactivity period
-- | - Refresh tokens have separate expiration
-- | - Session invalidation immediately revokes access
-- | - Session metadata tracked for security auditing
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Auth.Session as Session
-- |
-- | -- Create session
-- | session <- Session.createSession { userId: "user-123", ip: "127.0.0.1", userAgent: "..." } db logger
-- |
-- | -- Validate session
-- | result <- Session.validateSession session.id db logger
-- | case result of
-- |   Right session -> -- Session valid
-- |   Left err -> -- Session invalid
-- | ```
module Bridge.Auth.Session where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.DateTime (DateTime)
import Data.DateTime.Instant (Instant)
import Bridge.Auth.JWT (Claims)
import Bridge.FFI.Haskell.Database as DB
import Bridge.FFI.Node.Pino (Logger)

-- | Session data
type Session =
  { id :: String
  , userId :: String
  , accessToken :: String
  , refreshToken :: String
  , createdAt :: DateTime
  , expiresAt :: DateTime
  , refreshExpiresAt :: DateTime
  , lastActivityAt :: DateTime
  , ipAddress :: String
  , userAgent :: String
  , isActive :: Boolean
  }

-- | Session creation options
type CreateSessionOptions =
  { userId :: String
  , ipAddress :: String
  , userAgent :: String
  , expiresIn :: Maybe Int -- Seconds, default: 1 hour
  , refreshExpiresIn :: Maybe Int -- Seconds, default: 7 days
  }

-- | Session validation result
type SessionValidationResult =
  { valid :: Boolean
  , session :: Maybe Session
  , error :: Maybe String
  }

-- | Create new session
-- |
-- | **Purpose:** Creates a new user session with access and refresh tokens.
-- | **Parameters:**
-- | - `options`: User ID, IP, user agent, expiration times
-- | - `db`: Database handle
-- | - `logger`: Logger
-- | **Returns:** Either error or created session
createSession :: CreateSessionOptions -> DB.Database -> Logger -> Aff (Either String Session)
createSession options db logger = do
  result <- createSessionImpl options db logger
  pure result
  where
    foreign import createSessionImpl :: CreateSessionOptions -> DB.Database -> Logger -> Aff (Either String Session)

-- | Validate session
-- |
-- | **Purpose:** Checks if session exists, is active, and not expired.
-- | **Parameters:**
-- | - `sessionId`: Session identifier
-- | - `db`: Database handle
-- | - `logger`: Logger
-- | **Returns:** Either error or validated session
validateSession :: String -> DB.Database -> Logger -> Aff (Either String Session)
validateSession sessionId db logger = do
  result <- validateSessionImpl sessionId db logger
  pure result
  where
    foreign import validateSessionImpl :: String -> DB.Database -> Logger -> Aff (Either String Session)

-- | Refresh session
-- |
-- | **Purpose:** Creates new access token using refresh token.
-- | **Parameters:**
-- | - `refreshToken`: Refresh token string
-- | - `db`: Database handle
-- | - `logger`: Logger
-- | **Returns:** Either error or new session with updated tokens
refreshSession :: String -> DB.Database -> Logger -> Aff (Either String Session)
refreshSession refreshToken db logger = do
  result <- refreshSessionImpl refreshToken db logger
  pure result
  where
    foreign import refreshSessionImpl :: String -> DB.Database -> Logger -> Aff (Either String Session)

-- | Invalidate session
-- |
-- | **Purpose:** Immediately revokes session access.
-- | **Parameters:**
-- | - `sessionId`: Session identifier
-- | - `db`: Database handle
-- | - `logger`: Logger
-- | **Returns:** Either error or success
invalidateSession :: String -> DB.Database -> Logger -> Aff (Either String Unit)
invalidateSession sessionId db logger = do
  result <- invalidateSessionImpl sessionId db logger
  pure result
  where
    foreign import invalidateSessionImpl :: String -> DB.Database -> Logger -> Aff (Either String Unit)

-- | Update session activity
-- |
-- | **Purpose:** Updates last activity timestamp for session.
-- | **Parameters:**
-- | - `sessionId`: Session identifier
-- | - `db`: Database handle
-- | **Returns:** Either error or success
updateSessionActivity :: String -> DB.Database -> Aff (Either String Unit)
updateSessionActivity sessionId db = do
  result <- updateSessionActivityImpl sessionId db
  pure result
  where
    foreign import updateSessionActivityImpl :: String -> DB.Database -> Aff (Either String Unit)

-- | Get user sessions
-- |
-- | **Purpose:** Retrieves all active sessions for a user.
-- | **Parameters:**
-- | - `userId`: User identifier
-- | - `db`: Database handle
-- | **Returns:** Array of sessions
getUserSessions :: String -> DB.Database -> Aff (Array Session)
getUserSessions userId db = do
  sessions <- getUserSessionsImpl userId db
  pure sessions
  where
    foreign import getUserSessionsImpl :: String -> DB.Database -> Aff (Array Session)

-- | Cleanup expired sessions
-- |
-- | **Purpose:** Removes expired sessions from database.
-- | **Parameters:**
-- | - `db`: Database handle
-- | - `logger`: Logger
-- | **Returns:** Number of sessions removed
cleanupExpiredSessions :: DB.Database -> Logger -> Aff Int
cleanupExpiredSessions db logger = do
  count <- cleanupExpiredSessionsImpl db logger
  pure count
  where
    foreign import cleanupExpiredSessionsImpl :: DB.Database -> Logger -> Aff Int
