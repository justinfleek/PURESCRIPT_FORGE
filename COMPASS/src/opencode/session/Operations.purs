{-|
Module      : Opencode.Session.Operations
Description : Session CRUD operations with persistence
= Session Operations

Full session CRUD matching OpenCode's session/index.ts architecture.
Handles session creation, storage, and event publishing.

== Coeffect Equation

@
  create   : CreateInput -> Graded (Storage ⊗ Bus) SessionInfo
  get      : SessionID -> Graded Storage (Maybe SessionInfo)
  list     : Graded Storage (Array SessionInfo)
  messages : SessionID -> Graded Storage (Array MessageWithParts)
@

== Storage Layout

@
  storage/
  ├── session/{projectID}/{sessionID}     -> SessionInfo
  ├── message/{sessionID}/{messageID}     -> MessageInfo
  └── part/{messageID}/{partID}           -> Part
@

-}
module Opencode.Session.Operations
  ( -- * CRUD Operations
    create
  , get
  , list
  , update
  , remove
  , fork
  , touch
    -- * Message Operations
  , getMessages
  , updateMessage
  , removeMessage
  , updatePart
  , removePart
    -- * Utilities
  , isDefaultTitle
  , children
  , getUsage
    -- * State
  , SessionState(..)
  , initialState
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Map as Map
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Array as Array
import Data.String as String
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Class (liftEffect)

import Opencode.Types.Session (SessionInfo, SessionID, ProjectID, SessionTime)
import Opencode.Session.MessageV2 as MessageV2

-- ════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ════════════════════════════════════════════════════════════════════════════

-- | Message identifier
type MessageID = String

-- | Session system state
type SessionState =
  { sessions :: Map SessionID SessionInfo
  , messages :: Map SessionID (Map MessageID MessageV2.Info)
  , parts :: Map MessageID (Map String MessageV2.Part)
  , projectID :: ProjectID
  , directory :: String
  , abortFlags :: Map SessionID Boolean  -- Abort flags for session cancellation
  }

-- | Initial state
initialState :: ProjectID -> String -> SessionState
initialState projectId dir =
  { sessions: Map.empty
  , messages: Map.empty
  , parts: Map.empty
  , projectID: projectId
  , directory: dir
  , abortFlags: Map.empty
  }

-- ════════════════════════════════════════════════════════════════════════════
-- CREATE
-- ════════════════════════════════════════════════════════════════════════════

-- | Create input
type CreateInput =
  { parentID :: Maybe SessionID
  , title :: Maybe String
  }

-- | Create a new session
create :: CreateInput -> Ref SessionState -> Aff SessionInfo
create input stateRef = do
  state <- liftEffect $ Ref.read stateRef
  now <- liftEffect nowMillis
  
  let id = generateSessionId now
  let isChild = isJust input.parentID
  let title = fromMaybe (createDefaultTitle isChild now) input.title
  
  let session =
        { id
        , slug: generateSlug now
        , projectID: state.projectID
        , directory: state.directory
        , parentID: input.parentID
        , summary: Nothing
        , share: Nothing
        , title
        , version: "1.0.0"
        , time:
            { created: now
            , updated: now
            , compacting: Nothing
            , archived: Nothing
            }
        , permission: Nothing
        , revert: Nothing
        }
  
  -- Store session
  liftEffect $ Ref.modify_ (\s -> s { sessions = Map.insert id session s.sessions }) stateRef
  
  pure session

-- | Generate session ID (descending for natural ordering)
generateSessionId :: Number -> SessionID
generateSessionId now =
  "ses_" <> formatNumber (9999999999999.0 - now)

-- | Generate URL-friendly slug
generateSlug :: Number -> String
generateSlug now = "s" <> formatNumber now

-- | Format number as string (simplified)
formatNumber :: Number -> String
formatNumber n = show n

-- | Create default title
createDefaultTitle :: Boolean -> Number -> String
createDefaultTitle isChild now =
  let prefix = if isChild then "Child session - " else "New session - "
  in prefix <> formatTimestamp now

-- | Format timestamp (simplified)
formatTimestamp :: Number -> String
formatTimestamp n = show n

-- | Check if title is default
isDefaultTitle :: String -> Boolean
isDefaultTitle title =
  String.contains (String.Pattern "New session - ") title ||
  String.contains (String.Pattern "Child session - ") title

-- ════════════════════════════════════════════════════════════════════════════
-- READ
-- ════════════════════════════════════════════════════════════════════════════

-- | Get session by ID
get :: SessionID -> Ref SessionState -> Effect (Maybe SessionInfo)
get id stateRef = do
  state <- Ref.read stateRef
  pure $ Map.lookup id state.sessions

-- | List all sessions
list :: Ref SessionState -> Effect (Array SessionInfo)
list stateRef = do
  state <- Ref.read stateRef
  pure $ Array.fromFoldable $ Map.values state.sessions

-- | Get child sessions
children :: SessionID -> Ref SessionState -> Effect (Array SessionInfo)
children parentId stateRef = do
  sessions <- list stateRef
  pure $ Array.filter (\s -> s.parentID == Just parentId) sessions

-- ════════════════════════════════════════════════════════════════════════════
-- UPDATE
-- ════════════════════════════════════════════════════════════════════════════

-- | Update session
update :: SessionID -> (SessionInfo -> SessionInfo) -> Ref SessionState -> Aff (Maybe SessionInfo)
update id editor stateRef = do
  now <- liftEffect nowMillis
  liftEffect $ Ref.modify_ (updateSession now) stateRef
  liftEffect $ get id stateRef
  where
    updateSession now state =
      case Map.lookup id state.sessions of
        Nothing -> state
        Just session ->
          let updated = editor session
              withTime = updated { time = updated.time { updated = now } }
          in state { sessions = Map.insert id withTime state.sessions }

-- | Touch session (update timestamp only)
touch :: SessionID -> Ref SessionState -> Aff Unit
touch id stateRef = do
  _ <- update id identity stateRef
  pure unit

-- | Fork a session
fork :: { sessionID :: SessionID, messageID :: Maybe MessageID } -> Ref SessionState -> Aff (Either String SessionInfo)
fork input stateRef = do
  originalM <- liftEffect $ get input.sessionID stateRef
  case originalM of
    Nothing -> pure $ Left "Session not found"
    Just original -> do
      let forkedTitle = getForkedTitle original.title
      newSession <- create { parentID: Nothing, title: Just forkedTitle } stateRef
      -- Copy messages up to messageID
      msgs <- liftEffect $ getMessagesSync input.sessionID stateRef
      let msgsToFork = case input.messageID of
            Nothing -> msgs
            Just mid -> Array.takeWhile (\m -> m.id /= mid) msgs
      
      -- Copy messages and parts to new session
      state <- liftEffect $ Ref.read stateRef
      let newMessages = Array.foldl (\acc msg -> 
            Map.insert msg.id msg acc
          ) Map.empty msgsToFork
      
      -- Copy parts for each message
      let newParts = Array.foldl (\acc msg -> 
            case Map.lookup msg.id state.parts of
              Nothing -> acc
              Just partsMap -> Map.insert msg.id partsMap acc
          ) Map.empty msgsToFork
      
      -- Update state with copied messages and parts
      liftEffect $ Ref.modify_ (\s -> 
        s { messages = Map.insert newSession.id newMessages s.messages
          , parts = Map.union newParts s.parts
          }
      ) stateRef
      
      pure $ Right newSession

-- | Get forked title
getForkedTitle :: String -> String
getForkedTitle title =
  if String.contains (String.Pattern "(fork #") title
    then incrementForkNumber title
    else title <> " (fork #1)"

-- | Increment fork number in title
incrementForkNumber :: String -> String
incrementForkNumber title = title <> " (forked)"  -- Simplified

-- ════════════════════════════════════════════════════════════════════════════
-- DELETE
-- ════════════════════════════════════════════════════════════════════════════

-- | Remove session and all children
remove :: SessionID -> Ref SessionState -> Aff Unit
remove id stateRef = do
  -- Remove children first
  childSessions <- liftEffect $ children id stateRef
  _ <- traverseArray (\c -> remove c.id stateRef) childSessions
  
  -- Remove messages
  liftEffect $ Ref.modify_ (\s -> s { messages = Map.delete id s.messages }) stateRef
  
  -- Remove session
  liftEffect $ Ref.modify_ (\s -> s { sessions = Map.delete id s.sessions }) stateRef
  
  pure unit

-- ════════════════════════════════════════════════════════════════════════════
-- MESSAGES
-- ════════════════════════════════════════════════════════════════════════════

-- | Get messages for a session (sync version)
getMessagesSync :: SessionID -> Ref SessionState -> Effect (Array MessageV2.Info)
getMessagesSync sessionId stateRef = do
  state <- Ref.read stateRef
  case Map.lookup sessionId state.messages of
    Nothing -> pure []
    Just msgs -> pure $ Array.fromFoldable $ Map.values msgs

-- | Get messages for a session (with parts)
getMessages :: { sessionID :: SessionID, limit :: Maybe Int } -> Ref SessionState -> Aff (Array MessageV2.WithParts)
getMessages input stateRef = do
  state <- liftEffect $ Ref.read stateRef
  case Map.lookup input.sessionID state.messages of
    Nothing -> pure []
    Just msgMap -> do
      let msgs = Array.fromFoldable $ Map.values msgMap
      let limited = case input.limit of
            Nothing -> msgs
            Just n -> Array.take n msgs
      pure $ map (addParts state) limited
  where
    addParts state msg =
      let parts = case Map.lookup msg.id state.parts of
            Nothing -> []
            Just pm -> Array.fromFoldable $ Map.values pm
      in { info: msg, parts }

-- | Update a message
updateMessage :: MessageV2.Info -> Ref SessionState -> Aff MessageV2.Info
updateMessage msg stateRef = do
  liftEffect $ Ref.modify_ updateState stateRef
  pure msg
  where
    updateState state =
      let sessionMsgs = fromMaybe Map.empty $ Map.lookup msg.sessionID state.messages
          updated = Map.insert msg.id msg sessionMsgs
      in state { messages = Map.insert msg.sessionID updated state.messages }

-- | Remove a message
removeMessage :: { sessionID :: SessionID, messageID :: MessageID } -> Ref SessionState -> Aff Unit
removeMessage input stateRef = do
  liftEffect $ Ref.modify_ updateState stateRef
  pure unit
  where
    updateState state =
      case Map.lookup input.sessionID state.messages of
        Nothing -> state
        Just msgs ->
          let updated = Map.delete input.messageID msgs
          in state { messages = Map.insert input.sessionID updated state.messages }

-- | Update a message part
updatePart :: MessageV2.Part -> Ref SessionState -> Aff MessageV2.Part
updatePart part stateRef = do
  liftEffect $ Ref.modify_ updateState stateRef
  pure part
  where
    updateState state =
      let msgParts = fromMaybe Map.empty $ Map.lookup part.messageID state.parts
          updated = Map.insert part.id part msgParts
      in state { parts = Map.insert part.messageID updated state.parts }

-- | Remove a message part
removePart :: { messageID :: MessageID, partID :: String } -> Ref SessionState -> Aff Unit
removePart input stateRef = do
  liftEffect $ Ref.modify_ updateState stateRef
  pure unit
  where
    updateState state =
      case Map.lookup input.messageID state.parts of
        Nothing -> state
        Just parts ->
          let updated = Map.delete input.partID parts
          in state { parts = Map.insert input.messageID updated state.parts }

-- ════════════════════════════════════════════════════════════════════════════
-- USAGE CALCULATION
-- ════════════════════════════════════════════════════════════════════════════

-- | Token usage
type TokenUsage =
  { input :: Int
  , output :: Int
  , reasoning :: Int
  , cache :: { read :: Int, write :: Int }
  }

-- | Model cost
type ModelCost =
  { input :: Number
  , output :: Number
  , cache :: { read :: Number, write :: Number }
  }

-- | Calculate usage and cost
getUsage :: { model :: { cost :: ModelCost }, tokens :: TokenUsage } -> { cost :: Number, tokens :: TokenUsage }
getUsage input =
  let cost = calculateCost input.model.cost input.tokens
  in { cost, tokens: input.tokens }

-- | Calculate total cost
calculateCost :: ModelCost -> TokenUsage -> Number
calculateCost cost tokens =
  let inputCost = (toNumber tokens.input) * cost.input / 1000000.0
      outputCost = (toNumber tokens.output) * cost.output / 1000000.0
      cacheReadCost = (toNumber tokens.cache.read) * cost.cache.read / 1000000.0
      cacheWriteCost = (toNumber tokens.cache.write) * cost.cache.write / 1000000.0
  in inputCost + outputCost + cacheReadCost + cacheWriteCost

-- ════════════════════════════════════════════════════════════════════════════
-- HELPERS
-- ════════════════════════════════════════════════════════════════════════════

-- | Get current time in milliseconds
foreign import nowMillis :: Effect Number

-- | Convert Int to Number
toNumber :: Int -> Number
toNumber i = unsafeCoerce i
  where
    foreign import unsafeCoerce :: forall a b. a -> b

-- | Traverse array in Aff
traverseArray :: forall a b. (a -> Aff b) -> Array a -> Aff (Array b)
traverseArray f arr = case Array.uncons arr of
  Nothing -> pure []
  Just { head, tail } -> do
    b <- f head
    bs <- traverseArray f tail
    pure $ Array.cons b bs

-- ════════════════════════════════════════════════════════════════════════════
-- ABORT FLAGS
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if session is aborted
isAborted :: SessionID -> Ref SessionState -> Effect Boolean
isAborted sessionId stateRef = do
  state <- Ref.read stateRef
  pure $ fromMaybe false $ Map.lookup sessionId state.abortFlags

-- | Clear abort flag for session
clearAbort :: SessionID -> Ref SessionState -> Effect Unit
clearAbort sessionId stateRef = do
  Ref.modify_ (\s -> 
    s { abortFlags = Map.delete sessionId s.abortFlags }
  ) stateRef
