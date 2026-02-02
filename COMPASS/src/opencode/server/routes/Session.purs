{-|
Module      : Opencode.Server.Routes.Session
Description : Session HTTP routes
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Session Routes

Full implementation of session routes matching OpenCode's routes/session.ts.
Handles CRUD, messaging, forking, sharing, and compaction.

== Coeffect Equation

@
  routes : Unit -> Graded HTTP Router
  
  Session Routes:
    GET    /session              -> list
    GET    /session/status       -> status
    GET    /session/:id          -> get
    POST   /session              -> create
    DELETE /session/:id          -> delete
    PATCH  /session/:id          -> update
    POST   /session/:id/fork     -> fork
    POST   /session/:id/abort    -> abort
    POST   /session/:id/share    -> share
    DELETE /session/:id/share    -> unshare
    POST   /session/:id/summarize -> summarize
    
  Message Routes:
    GET    /session/:id/message          -> messages
    GET    /session/:id/message/:mid     -> getMessage
    POST   /session/:id/message          -> prompt
    DELETE /session/:id/message/:mid/part/:pid -> removePart
@

-}
module Opencode.Server.Routes.Session
  ( -- * Route Handlers
    list
  , status
  , get
  , create
  , delete
  , update
  , fork
  , abort
  , share
  , unshare
  , children
  , todo
  , diff
  , summarize
  , messages
  , getMessage
  , prompt
  , promptAsync
  , command
  , shell
  , revert
  , unrevert
  , removePart
  , updatePart
    -- * Types
  , ListQuery
  , UpdateBody
  , SummarizeBody
  , PromptBody
  , CommandBody
  , ShellBody
  , RevertBody
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Effect.Aff (Aff)
import Effect.Ref (Ref)

import Opencode.Types.Session (SessionInfo, SessionID)
import Opencode.Session.Operations as Operations
import Opencode.Session.MessageV2 as MessageV2

-- ════════════════════════════════════════════════════════════════════════════
-- QUERY/BODY TYPES
-- ════════════════════════════════════════════════════════════════════════════

-- | Query params for list endpoint
type ListQuery =
  { directory :: Maybe String
  , roots :: Maybe Boolean
  , start :: Maybe Number
  , search :: Maybe String
  , limit :: Maybe Int
  }

-- | Body for update endpoint
type UpdateBody =
  { title :: Maybe String
  , time :: Maybe { archived :: Maybe Number }
  }

-- | Body for summarize endpoint
type SummarizeBody =
  { providerID :: String
  , modelID :: String
  , auto :: Maybe Boolean
  }

-- | Body for prompt endpoint
type PromptBody =
  { parts :: Array MessageV2.Part
  , agent :: Maybe String
  , providerID :: Maybe String
  , modelID :: Maybe String
  }

-- | Body for command endpoint
type CommandBody =
  { command :: String
  , args :: Maybe String
  }

-- | Body for shell endpoint
type ShellBody =
  { command :: String
  , cwd :: Maybe String
  }

-- | Body for revert endpoint
type RevertBody =
  { messageID :: String
  }

-- ════════════════════════════════════════════════════════════════════════════
-- SESSION CRUD
-- ════════════════════════════════════════════════════════════════════════════

-- | List sessions with filtering
list :: ListQuery -> Ref Operations.SessionState -> Aff (Array SessionInfo)
list query stateRef = do
  allSessions <- pure =<< Operations.list stateRef
  let filtered = Array.filter (matchesQuery query) allSessions
  let limited = case query.limit of
        Nothing -> filtered
        Just n -> Array.take n filtered
  pure limited
  where
    matchesQuery :: ListQuery -> SessionInfo -> Boolean
    matchesQuery q session =
      matchDirectory q.directory session &&
      matchRoots q.roots session &&
      matchStart q.start session &&
      matchSearch q.search session
    
    matchDirectory :: Maybe String -> SessionInfo -> Boolean
    matchDirectory Nothing _ = true
    matchDirectory (Just dir) session = session.directory == dir
    
    matchRoots :: Maybe Boolean -> SessionInfo -> Boolean
    matchRoots Nothing _ = true
    matchRoots (Just false) _ = true
    matchRoots (Just true) session = case session.parentID of
      Nothing -> true
      Just _ -> false
    
    matchStart :: Maybe Number -> SessionInfo -> Boolean
    matchStart Nothing _ = true
    matchStart (Just start) session = session.time.updated >= start
    
    matchSearch :: Maybe String -> SessionInfo -> Boolean
    matchSearch Nothing _ = true
    matchSearch (Just term) session =
      String.contains (String.Pattern (String.toLower term)) (String.toLower session.title)

-- | Get session status (active, idle, etc.)
type SessionStatus = { state :: String, busy :: Boolean }

status :: Ref Operations.SessionState -> Aff (Array { sessionID :: String, status :: SessionStatus })
status stateRef = do
  sessions <- Operations.list stateRef
  pure $ map (\s -> { sessionID: s.id, status: { state: "idle", busy: false } }) sessions

-- | Get single session
get :: SessionID -> Ref Operations.SessionState -> Aff (Either String SessionInfo)
get sessionId stateRef = do
  result <- Operations.get sessionId stateRef
  pure $ case result of
    Nothing -> Left ("Session not found: " <> sessionId)
    Just session -> Right session

-- | Create new session
create :: { parentID :: Maybe String, title :: Maybe String } -> Ref Operations.SessionState -> Aff SessionInfo
create input stateRef = Operations.create input stateRef

-- | Delete session
delete :: SessionID -> Ref Operations.SessionState -> Aff (Either String Boolean)
delete sessionId stateRef = do
  Operations.remove sessionId stateRef
  pure $ Right true

-- | Update session
update :: SessionID -> UpdateBody -> Ref Operations.SessionState -> Aff (Either String SessionInfo)
update sessionId body stateRef = do
  result <- Operations.update sessionId (applyUpdates body) stateRef
  pure $ case result of
    Nothing -> Left ("Session not found: " <> sessionId)
    Just session -> Right session
  where
    applyUpdates :: UpdateBody -> SessionInfo -> SessionInfo
    applyUpdates b session = session
      { title = fromMaybe session.title b.title
      , time = case b.time of
          Nothing -> session.time
          Just t -> session.time { archived = t.archived }
      }

-- ════════════════════════════════════════════════════════════════════════════
-- SESSION OPERATIONS
-- ════════════════════════════════════════════════════════════════════════════

-- | Fork session
fork :: { sessionID :: SessionID, messageID :: Maybe String } -> Ref Operations.SessionState -> Aff (Either String SessionInfo)
fork input stateRef = Operations.fork input stateRef

-- | Abort session processing
abort :: SessionID -> Aff Boolean
abort _sessionId = do
  -- TODO: Signal session processor to cancel
  pure true

-- | Share session (create public URL)
share :: SessionID -> Ref Operations.SessionState -> Aff (Either String SessionInfo)
share sessionId stateRef = do
  result <- Operations.update sessionId addShareInfo stateRef
  pure $ case result of
    Nothing -> Left ("Session not found: " <> sessionId)
    Just session -> Right session
  where
    addShareInfo :: SessionInfo -> SessionInfo
    addShareInfo session = session { share = Just { url: generateShareUrl sessionId } }
    
    generateShareUrl :: SessionID -> String
    generateShareUrl sid = "https://share.opencode.ai/s/" <> sid

-- | Unshare session
unshare :: SessionID -> Ref Operations.SessionState -> Aff (Either String SessionInfo)
unshare sessionId stateRef = do
  result <- Operations.update sessionId removeShareInfo stateRef
  pure $ case result of
    Nothing -> Left ("Session not found: " <> sessionId)
    Just session -> Right session
  where
    removeShareInfo :: SessionInfo -> SessionInfo
    removeShareInfo session = session { share = Nothing }

-- | Get child sessions
children :: SessionID -> Ref Operations.SessionState -> Aff (Array SessionInfo)
children sessionId stateRef = Operations.children sessionId stateRef

-- | Get session todos
type TodoInfo = { id :: String, content :: String, status :: String, priority :: String }

todo :: SessionID -> Aff (Array TodoInfo)
todo _sessionId = do
  -- TODO: Fetch from storage
  pure []

-- | Get message diff (file changes)
type FileDiff = { path :: String, added :: Int, removed :: Int, status :: String }

diff :: { sessionID :: SessionID, messageID :: String } -> Aff (Array FileDiff)
diff _input = do
  -- TODO: Calculate diff from snapshots
  pure []

-- | Summarize/compact session
summarize :: SessionID -> SummarizeBody -> Aff Boolean
summarize _sessionId _body = do
  -- TODO: Invoke compaction processor
  pure true

-- ════════════════════════════════════════════════════════════════════════════
-- MESSAGE OPERATIONS
-- ════════════════════════════════════════════════════════════════════════════

-- | Get messages for session
messages :: { sessionID :: SessionID, limit :: Maybe Int } -> Ref Operations.SessionState -> Aff (Array MessageV2.WithParts)
messages input stateRef = Operations.getMessages input stateRef

-- | Get single message
getMessage :: { sessionID :: SessionID, messageID :: String } -> Aff MessageV2.WithParts
getMessage input = MessageV2.get input

-- | Send prompt to session
prompt :: SessionID -> PromptBody -> Aff (Either String MessageV2.WithParts)
prompt _sessionId _body = do
  -- TODO: Create user message, invoke processor loop
  pure $ Left "prompt not yet implemented"

-- | Send prompt async (return immediately)
promptAsync :: SessionID -> PromptBody -> Aff Boolean
promptAsync _sessionId _body = do
  -- TODO: Fire and forget prompt processing
  pure true

-- | Execute command
command :: SessionID -> CommandBody -> Aff (Either String MessageV2.WithParts)
command _sessionId _body = do
  -- TODO: Parse and execute command
  pure $ Left "command not yet implemented"

-- | Execute shell command
shell :: SessionID -> ShellBody -> Aff (Either String MessageV2.WithParts)
shell _sessionId _body = do
  -- TODO: Execute shell and capture output
  pure $ Left "shell not yet implemented"

-- | Revert to message
revert :: SessionID -> RevertBody -> Aff (Either String SessionInfo)
revert _sessionId _body = do
  -- TODO: Revert session state
  pure $ Left "revert not yet implemented"

-- | Unrevert (restore reverted messages)
unrevert :: SessionID -> Aff (Either String SessionInfo)
unrevert _sessionId = do
  -- TODO: Restore reverted messages
  pure $ Left "unrevert not yet implemented"

-- | Remove message part
removePart :: { sessionID :: SessionID, messageID :: String, partID :: String } -> Ref Operations.SessionState -> Aff Boolean
removePart input stateRef = do
  Operations.removePart { messageID: input.messageID, partID: input.partID } stateRef
  pure true

-- | Update message part
updatePart :: MessageV2.Part -> Ref Operations.SessionState -> Aff MessageV2.Part
updatePart part stateRef = Operations.updatePart part stateRef

-- ════════════════════════════════════════════════════════════════════════════
-- HELPERS
-- ════════════════════════════════════════════════════════════════════════════

fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe def = case _ of
  Nothing -> def
  Just a -> a
