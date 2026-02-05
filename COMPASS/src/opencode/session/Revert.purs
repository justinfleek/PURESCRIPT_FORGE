-- | Session Revert - revert to previous state
module Opencode.Session.Revert where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Array as Array
import Effect.Ref (Ref)
import Opencode.Session.Operations as Operations

-- | Revert result
type RevertResult =
  { messagesRemoved :: Int
  , revertedToId :: String
  }

-- | Revert to a specific message
-- | Removes all messages after the specified message
revertToMessage :: String -> String -> Ref Operations.SessionState -> Aff (Either String RevertResult)
revertToMessage sessionId messageId stateRef = do
  -- Get all messages for the session
  messages <- Operations.getMessages { sessionID: sessionId, limit: Nothing } stateRef
  
  -- Find the message to revert to
  let messageIndex = Array.findIndex (\m -> m.info.id == messageId) messages
  
  case messageIndex of
    Nothing -> pure $ Left "Message not found"
    Just idx -> do
      -- Remove all messages after this one
      let messagesToRemove = Array.drop (idx + 1) messages
      let count = Array.length messagesToRemove
      _ <- Array.traverse (\m -> Operations.removeMessage { sessionID: sessionId, messageID: m.info.id } stateRef) messagesToRemove
      
      pure $ Right
        { messagesRemoved: count
        , revertedToId: messageId
        }

-- | Revert last N messages
revertLast :: String -> Int -> Ref Operations.SessionState -> Aff (Either String RevertResult)
revertLast sessionId count stateRef = do
  if count <= 0
    then pure $ Left "Count must be positive"
    else do
      -- Get all messages for the session
      messages <- Operations.getMessages { sessionID: sessionId, limit: Nothing } stateRef
      
      if Array.length messages < count
        then pure $ Left "Not enough messages to revert"
        else do
          -- Get the message ID to revert to (the one before the last N)
          let targetIndex = Array.length messages - count - 1
          case Array.index messages targetIndex of
            Nothing -> pure $ Left "Cannot determine revert target"
            Just targetMsg -> do
              -- Remove the last N messages
              let messagesToRemove = Array.take count (Array.reverse messages)
              _ <- Array.traverse (\m -> Operations.removeMessage { sessionID: sessionId, messageID: m.info.id } stateRef) messagesToRemove
              
              pure $ Right
                { messagesRemoved: count
                , revertedToId: targetMsg.info.id
                }

-- | Undo last action
-- | Removes the last message
undo :: String -> Ref Operations.SessionState -> Aff (Either String RevertResult)
undo sessionId stateRef = do
  -- Get all messages for the session
  messages <- Operations.getMessages { sessionID: sessionId, limit: Nothing } stateRef
  
  if Array.null messages
    then pure $ Left "No messages to undo"
    else do
      -- Get the last message and the one before it
      let lastMsg = Array.last messages
      let secondLastIndex = Array.length messages - 2
      let targetMsg = Array.index messages secondLastIndex
      
      case lastMsg of
        Nothing -> pure $ Left "No messages found"
        Just msg -> do
          -- Remove the last message
          _ <- Operations.removeMessage { sessionID: sessionId, messageID: msg.info.id } stateRef
          
          let revertedToId = case targetMsg of
                Nothing -> ""
                Just tm -> tm.info.id
          
          pure $ Right
            { messagesRemoved: 1
            , revertedToId: revertedToId
            }
