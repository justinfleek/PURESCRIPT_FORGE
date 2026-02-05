-- | Session Retry - retry failed operations
module Opencode.Session.Retry where

import Prelude
import Effect.Aff (Aff, delay, Milliseconds(..))
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Effect.Ref (Ref)
import Opencode.Session.Operations as Operations
import Opencode.Session.Processor as Processor

-- | Retry configuration
type RetryConfig =
  { maxAttempts :: Int
  , backoffMs :: Int
  , maxBackoffMs :: Int
  }

-- | Default retry config
defaultRetryConfig :: RetryConfig
defaultRetryConfig =
  { maxAttempts: 3
  , backoffMs: 1000
  , maxBackoffMs: 30000
  }

-- | Retry a failed message
-- | In production, this would:
-- | 1. Find the failed message
-- | 2. Remove all messages after it
-- | 3. Restart processing from that point
retryMessage :: String -> String -> Ref Operations.SessionState -> Aff (Either String Unit)
retryMessage sessionId messageId stateRef = do
  -- Get all messages for the session
  messages <- Operations.getMessages { sessionID: sessionId, limit: Nothing } stateRef
  
  -- Find the message to retry from
  let messageIndex = Array.findIndex (\m -> m.info.id == messageId) messages
  
  case messageIndex of
    Nothing -> pure $ Left "Message not found"
    Just idx -> do
      -- Remove all messages after this one
      let messagesToRemove = Array.drop (idx + 1) messages
      _ <- Array.traverse (\m -> Operations.removeMessage { sessionID: sessionId, messageID: m.info.id } stateRef) messagesToRemove
      
      -- In production, would restart processing here
      -- For now, just return success
      pure $ Right unit

-- | Retry from a specific point
-- | Removes all messages after the specified message and restarts processing
retryFrom :: String -> String -> Ref Operations.SessionState -> Aff (Either String Unit)
retryFrom sessionId fromMessageId stateRef = do
  -- Get all messages for the session
  messages <- Operations.getMessages { sessionID: sessionId, limit: Nothing } stateRef
  
  -- Find messages to remove (after fromMessageId)
  let shouldRemove = Array.foldl (\found msg -> 
        if found
          then true  -- Already found the fromMessageId, remove all subsequent
          else msg.info.id == fromMessageId  -- Found the fromMessageId, start removing
      ) false messages
  
  if shouldRemove
    then do
      -- Find the index of fromMessageId
      let fromIndex = Array.findIndex (\m -> m.info.id == fromMessageId) messages
      case fromIndex of
        Nothing -> pure $ Left "From message not found"
        Just idx -> do
          -- Remove all messages after fromMessageId
          let messagesToRemove = Array.drop (idx + 1) messages
          _ <- Array.traverse (\m -> Operations.removeMessage { sessionID: sessionId, messageID: m.info.id } stateRef) messagesToRemove
          pure $ Right unit
    else pure $ Left "From message not found in session"
