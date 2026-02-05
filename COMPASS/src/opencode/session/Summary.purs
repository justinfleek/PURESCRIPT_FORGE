-- | Session Summary - generate session summaries
module Opencode.Session.Summary where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.Set as Set
import Data.String as String
import Data.Map as Map
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Opencode.Session.Operations as Operations
import Opencode.Session.MessageV2 as MessageV2
import Opencode.Session.MessageV2Types (Part(..), WithParts)

-- | Session summary
type SessionSummary =
  { sessionId :: String
  , title :: String
  , description :: String
  , messageCount :: Int
  , toolsUsed :: Array String
  , filesModified :: Array String
  , createdAt :: Number
  , updatedAt :: Number
  }

-- | Summary storage (in production, would be part of SessionState)
summaryStorageRef :: Ref (Map.Map String SessionSummary)
summaryStorageRef = unsafePerformEffect $ Ref.new Map.empty

-- | Generate a summary for a session
generateSummary :: String -> Ref Operations.SessionState -> Aff (Either String SessionSummary)
generateSummary sessionId stateRef = do
  -- Get session info
  sessionM <- liftEffect $ Operations.get sessionId stateRef
  case sessionM of
    Nothing -> pure $ Left "Session not found"
    Just session -> do
      -- Get messages
      messages <- Operations.getMessages { sessionID: sessionId, limit: Nothing } stateRef
      
      -- Analyze messages to extract information
      let messageCount = Array.length messages
      let toolsUsed = extractToolsUsed messages
      let filesModified = extractFilesModified messages
      
      -- Generate description from first few messages
      let description = generateDescription messages
      
      -- Create summary
      let summary =
            { sessionId: sessionId
            , title: session.title
            , description: description
            , messageCount: messageCount
            , toolsUsed: Array.fromFoldable toolsUsed
            , filesModified: Array.fromFoldable filesModified
            , createdAt: session.time.created
            , updatedAt: session.time.updated
            }
      
      -- Store summary
      liftEffect $ Ref.modify_ (\storage -> Map.insert sessionId summary storage) summaryStorageRef
      
      pure $ Right summary
  where
    extractToolsUsed :: Array WithParts -> Set.Set String
    extractToolsUsed messages =
      Array.foldMap (\msg ->
        Array.foldMap (\part ->
          case part of
            PartTool tool -> Set.singleton tool.tool
            _ -> Set.empty
        ) msg.parts
      ) messages
    
    extractFilesModified :: Array WithParts -> Set.Set String
    extractFilesModified messages =
      Array.foldMap (\msg ->
        Array.foldMap (\part ->
          case part of
            PartFile file -> Set.singleton file.path
            PartPatch patch -> Set.singleton patch.path
            _ -> Set.empty
        ) msg.parts
      ) messages
    
    generateDescription :: Array WithParts -> String
    generateDescription messages =
      if Array.null messages
        then "Empty session"
        else
          let firstMsg = Array.head messages
          in case firstMsg of
            Nothing -> "Session with " <> show (Array.length messages) <> " messages"
            Just msg -> "Session started: " <> String.take 100 (extractTextFromMessage msg)
    
    extractTextFromMessage :: WithParts -> String
    extractTextFromMessage msg =
      Array.foldMap (\part ->
        case part of
          PartText text -> text.content
          _ -> ""
      ) msg.parts

-- | Get existing summary
getSummary :: String -> Aff (Either String (Maybe SessionSummary))
getSummary sessionId = do
  storage <- liftEffect $ Ref.read summaryStorageRef
  pure $ Right $ Map.lookup sessionId storage
