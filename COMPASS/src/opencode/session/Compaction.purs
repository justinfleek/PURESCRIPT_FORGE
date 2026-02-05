-- | Session Compaction - compress old messages
module Opencode.Session.Compaction where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.String as String
import Effect.Ref (Ref)
import Opencode.Session.Operations as Operations
import Opencode.Session.MessageV2Types (Part(..), WithParts)

-- | Compaction configuration
type CompactionConfig =
  { maxMessages :: Int
  , summaryModel :: Maybe String
  , preserveSystemMessages :: Boolean
  }

-- | Compacted message summary
type CompactionResult =
  { originalCount :: Int
  , compactedCount :: Int
  , summary :: String
  }

-- | Compact session messages
compact :: String -> CompactionConfig -> Ref Operations.SessionState -> Aff (Either String CompactionResult)
compact sessionId config stateRef = do
  -- Get all messages
  messages <- Operations.getMessages { sessionID: sessionId, limit: Nothing } stateRef
  let originalCount = Array.length messages
  
  if originalCount <= config.maxMessages
    then pure $ Right
      { originalCount
      , compactedCount: originalCount
      , summary: "No compaction needed"
      }
    else do
      -- Keep system messages if preserveSystemMessages is true
      let (systemMsgs, regularMsgs) = if config.preserveSystemMessages
            then partitionSystemMessages messages
            else ([], messages)
      
      -- Keep the most recent maxMessages regular messages
      let keepCount = config.maxMessages - Array.length systemMsgs
      let messagesToKeep = Array.take keepCount (Array.reverse regularMsgs) # Array.reverse
      let messagesToRemove = Array.drop keepCount regularMsgs
      
      -- Generate summary of removed messages
      let summary = generateCompactionSummary messagesToRemove
      
      -- Remove old messages
      _ <- Array.traverse (\m -> Operations.removeMessage { sessionID: sessionId, messageID: m.info.id } stateRef) messagesToRemove
      
      let compactedCount = Array.length systemMsgs + Array.length messagesToKeep
      
      pure $ Right
        { originalCount
        , compactedCount
        , summary
        }
  where
    partitionSystemMessages :: Array WithParts -> (Array WithParts, Array WithParts)
    partitionSystemMessages msgs =
      Array.partition (\msg ->
        Array.any (\part ->
          case part of
            PartText text -> String.contains (String.Pattern "system") (String.toLower text.content)
            _ -> false
        ) msg.parts
      ) msgs
    
    generateCompactionSummary :: Array WithParts -> String
    generateCompactionSummary removed =
      "Compacted " <> show (Array.length removed) <> " messages. " <>
      "Summary: " <> String.take 200 (String.joinWith " " (Array.map (extractTextFromMessage) removed))
    
    extractTextFromMessage :: WithParts -> String
    extractTextFromMessage msg =
      Array.foldMap (\part ->
        case part of
          PartText text -> text.content <> " "
          _ -> ""
      ) msg.parts

-- | Check if compaction is needed
needsCompaction :: String -> Int -> Ref Operations.SessionState -> Aff Boolean
needsCompaction sessionId threshold stateRef = do
  messages <- Operations.getMessages { sessionID: sessionId, limit: Nothing } stateRef
  pure $ Array.length messages > threshold
