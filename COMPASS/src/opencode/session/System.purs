-- | Session System - system message handling
module Opencode.Session.System where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String

-- | Build the system message for a session
buildSystemMessage :: String -> Aff (Either String String)
buildSystemMessage sessionId = do
  -- Get base system prompt
  let basePrompt = getBaseSystemPrompt
  
  -- Get environment information
  envInfo <- getEnvironmentInfo
  
  -- Combine base prompt with environment info
  let systemMessage = basePrompt <> "\n\n" <> envInfo
  
  pure $ Right systemMessage
  where
    getEnvironmentInfo :: Aff String
    getEnvironmentInfo = do
      platform <- liftEffect getPlatform
      date <- liftEffect getCurrentDate
      cwd <- liftEffect getCurrentWorkingDirectory
      
      pure $ String.joinWith "\n"
        [ "Environment information:"
        , "  Platform: " <> platform
        , "  Date: " <> date
        , "  Working directory: " <> cwd
        ]
    
    foreign import getPlatform :: Effect String
    foreign import getCurrentDate :: Effect String
    foreign import getCurrentWorkingDirectory :: Effect String

-- | Get base system prompt
getBaseSystemPrompt :: String
getBaseSystemPrompt = 
  "You are an AI coding assistant. Help users with software engineering tasks. " <>
  "Use the available tools to complete tasks. Be concise and accurate. " <>
  "Follow best practices and write clean, maintainable code."

-- | Append context to system message
appendContext :: String -> String -> String
appendContext systemMsg context = systemMsg <> "\n\n" <> context
