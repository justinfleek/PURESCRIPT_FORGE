{-|
Module      : Forge.ACP.Session
Description : Agent Control Protocol - Session Management

ACP Sessions represent active communication channels between the system
and AI agents. Each session maintains state, history, and handles
message routing.

== Coeffect Equation

@
  create : String -> Graded (State * Agent) ACPSession
  send   : String -> Message -> Graded (State * Network) Response
  close  : String -> Graded State Unit
@

== Session Lifecycle

1. Create session with agent ID
2. Send/receive messages
3. Close session (cleanup resources)
-}
module Forge.ACP.Session
  ( -- * Types
    ACPSession
  , SessionStatus(..)
  , SessionMessage
  , SessionConfig
    -- * Session Operations
  , create
  , get
  , close
  , closeAll
    -- * Messaging
  , send
  , receive
  , getHistory
    -- * Status
  , getStatus
  , listActive
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Session status
data SessionStatus
  = SessionCreating
  | SessionActive
  | SessionPaused
  | SessionClosing
  | SessionClosed
  | SessionError String

derive instance eqSessionStatus :: Eq SessionStatus

instance showSessionStatus :: Show SessionStatus where
  show SessionCreating = "creating"
  show SessionActive = "active"
  show SessionPaused = "paused"
  show SessionClosing = "closing"
  show SessionClosed = "closed"
  show (SessionError e) = "error: " <> e

-- | Session configuration
type SessionConfig =
  { timeout :: Int           -- Session timeout in ms
  , maxHistory :: Int        -- Maximum messages to keep
  , streaming :: Boolean     -- Enable streaming
  }

-- | Session message
type SessionMessage =
  { id :: String
  , role :: String           -- "user", "assistant", "system"
  , content :: String
  , timestamp :: Number
  }

-- | ACP Session
type ACPSession =
  { id :: String
  , agentId :: String
  , status :: SessionStatus
  , config :: SessionConfig
  , createdAt :: Number
  , lastActivity :: Number
  }

-- ============================================================================
-- FFI
-- ============================================================================

-- | Create session in store
foreign import createSessionFFI :: String -> String -> SessionConfig -> Aff (Either String ACPSession)

-- | Get session from store
foreign import getSessionFFI :: String -> Aff (Maybe ACPSession)

-- | Update session status
foreign import updateSessionStatusFFI :: String -> String -> Aff (Either String Unit)

-- | Close session
foreign import closeSessionFFI :: String -> Aff (Either String Unit)

-- | Get all active sessions
foreign import getActiveSessionsFFI :: Aff (Array ACPSession)

-- | Add message to session history
foreign import addMessageFFI :: String -> SessionMessage -> Aff (Either String Unit)

-- | Get session message history
foreign import getMessagesFFI :: String -> Aff (Array SessionMessage)

-- | Generate unique ID
foreign import generateIdFFI :: Aff String

-- ============================================================================
-- DEFAULT CONFIG
-- ============================================================================

defaultConfig :: SessionConfig
defaultConfig =
  { timeout: 30000      -- 30 seconds
  , maxHistory: 100     -- Keep last 100 messages
  , streaming: true     -- Enable streaming by default
  }

-- ============================================================================
-- SESSION OPERATIONS
-- ============================================================================

{-| Create a new ACP session.

Creates a session for the specified agent with default configuration.
-}
create :: String -> Aff (Either String ACPSession)
create agentId = do
  sessionId <- generateIdFFI
  createSessionFFI sessionId agentId defaultConfig

{-| Get an existing session by ID. -}
get :: String -> Aff (Either String ACPSession)
get sessionId = do
  result <- getSessionFFI sessionId
  case result of
    Nothing -> pure $ Left ("Session not found: " <> sessionId)
    Just session -> pure $ Right session

{-| Close a session.

Marks session as closed and cleans up resources.
-}
close :: String -> Aff (Either String Unit)
close sessionId = do
  -- Update status to closing
  _ <- updateSessionStatusFFI sessionId "closing"
  -- Close the session
  closeSessionFFI sessionId

{-| Close all active sessions. -}
closeAll :: Aff (Either String Int)
closeAll = do
  sessions <- getActiveSessionsFFI
  results <- traverse (\s -> close s.id) sessions
  let closed = Array.length $ Array.filter isRight results
  pure $ Right closed
  where
    isRight (Right _) = true
    isRight (Left _) = false

-- ============================================================================
-- MESSAGING
-- ============================================================================

{-| Send a message in a session.

Adds the message to history and returns. In production, this would
route to the agent.
-}
send :: String -> String -> String -> Aff (Either String Unit)
send sessionId role content = do
  msgId <- generateIdFFI
  let msg = 
        { id: msgId
        , role
        , content
        , timestamp: 0.0  -- Set by FFI
        }
  addMessageFFI sessionId msg

{-| Receive messages (get recent history). -}
receive :: String -> Int -> Aff (Either String (Array SessionMessage))
receive sessionId limit = do
  messages <- getMessagesFFI sessionId
  pure $ Right $ Array.take limit messages

{-| Get full message history for a session. -}
getHistory :: String -> Aff (Either String (Array SessionMessage))
getHistory sessionId = do
  session <- getSessionFFI sessionId
  case session of
    Nothing -> pure $ Left ("Session not found: " <> sessionId)
    Just _ -> do
      messages <- getMessagesFFI sessionId
      pure $ Right messages

-- ============================================================================
-- STATUS
-- ============================================================================

{-| Get session status. -}
getStatus :: String -> Aff (Maybe SessionStatus)
getStatus sessionId = do
  result <- getSessionFFI sessionId
  pure $ map _.status result

{-| List all active sessions. -}
listActive :: Aff (Array ACPSession)
listActive = do
  sessions <- getActiveSessionsFFI
  pure $ Array.filter isActive sessions
  where
    isActive session = case session.status of
      SessionActive -> true
      SessionPaused -> true
      _ -> false

-- ============================================================================
-- HELPERS
-- ============================================================================

traverse :: forall a b. (a -> Aff b) -> Array a -> Aff (Array b)
traverse f arr = traverseImpl f arr

foreign import traverseImpl :: forall a b. (a -> Aff b) -> Array a -> Aff (Array b)
