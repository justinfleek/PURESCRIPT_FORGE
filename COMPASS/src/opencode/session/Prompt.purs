-- | Session Prompt - handle user prompts
module Opencode.Session.Prompt where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Array as Array
import Effect.Ref (Ref)
import Opencode.Session.Processor as Processor
import Opencode.Session.LLM as LLM
import Opencode.Session.Operations as Operations
import Opencode.Session.MessageV2Types as MessageV2Types
import Opencode.Session.MessageV2 as MessageV2
import Opencode.Types.Tool (ToolInfo)
import Bridge.FFI.Node.Terminal as Terminal

-- | Prompt request
type PromptRequest =
  { sessionId :: String
  , text :: String
  , files :: Array String
  , model :: Maybe String
  , agent :: Maybe String
  }

-- | Prompt context (required dependencies)
type PromptContext =
  { sessionState :: Ref Operations.SessionState
  , processorConfig :: Processor.ProcessorConfig
  }

-- | Send a prompt to a session
sendPrompt :: PromptRequest -> PromptContext -> Aff (Either String Unit)
sendPrompt request ctx = do
  -- 1. Generate message ID and timestamp
  now <- liftEffect Operations.nowMillis
  let messageId = "msg_" <> show now
  
  -- 2. Create user message
  let userMessage = MessageV2Types.InfoUser
        { id: messageId
        , sessionID: request.sessionId
        , role: "user"
        , time: { created: now }
        , summary: Nothing
        , agent: fromMaybe "default" request.agent
        , model: { providerID: "openai", modelID: fromMaybe "gpt-4" request.model }
        , system: Nothing
        , tools: Nothing
        , variant: Nothing
        }
  
  -- 3. Create text part for the prompt
  let textPart = MessageV2Types.PartText
        { id: "part_" <> messageId
        , sessionID: request.sessionId
        , messageID: messageId
        , text: request.text
        , synthetic: Nothing
        , ignored: Nothing
        , time: Nothing
        , metadata: Nothing
        }
  
  -- 4. Add message to session state
  _ <- Operations.updateMessage userMessage ctx.sessionState
  
  -- 5. Add text part
  _ <- Operations.updatePart (MessageV2Types.PartText textPart) ctx.sessionState
  
  -- 6. Update processor config with model if provided
  let updatedConfig = ctx.processorConfig
        { model = fromMaybe ctx.processorConfig.model request.model
        , agent = request.agent <|> ctx.processorConfig.agent
        }
  
  -- 7. Trigger processing loop
  result <- Processor.startProcessing updatedConfig
  
  case result of
    Left err -> pure $ Left ("Failed to start processing: " <> err)
    Right _ -> pure $ Right unit

-- | Execute a command in a session
executeCommand :: String -> String -> String -> PromptContext -> Aff (Either String Unit)
executeCommand sessionId command args ctx = do
  -- 1. Execute command via Terminal
  result <- Terminal.executeCommand (command <> " " <> args) Nothing Nothing
  
  -- 2. Generate message ID and timestamp
  now <- liftEffect Operations.nowMillis
  let messageId = "msg_" <> show now
  
  -- 3. Create assistant message with command result
  let assistantMessage = MessageV2Types.InfoAssistant
        { id: messageId
        , sessionID: sessionId
        , role: "assistant"
        , time: { created: now, completed: Just now }
        , error: Nothing
        , parentID: ""  -- Would track parent message (requires message history)
        , modelID: ctx.processorConfig.model
        , providerID: "system"
        , mode: "command"
        , agent: fromMaybe "default" ctx.processorConfig.agent
        , path: { cwd: getCurrentWorkingDirectory, root: getProjectRoot }  -- Get from session or environment
  where
    getCurrentWorkingDirectory :: String
    getCurrentWorkingDirectory = 
      -- Would get from session state or process environment
      -- For now, return empty - requires session context
      ""
    
    getProjectRoot :: String
    getProjectRoot =
      -- Would get from session state or detect from file system
      -- For now, return empty - requires session context
      ""
        , summary: Nothing
        , cost: 0.0
        , tokens: { prompt: 0, completion: 0, total: 0 }
        , finish: Just "stop"
        }
  
  -- 4. Create text part with command output
  let outputText = case result of
        Left err -> "Error: " <> err
        Right response -> fromMaybe "" response.output
  
  let textPart = MessageV2Types.PartText
        { id: "part_" <> messageId
        , sessionID: sessionId
        , messageID: messageId
        , text: outputText
        , synthetic: Nothing
        , ignored: Nothing
        , time: Nothing
        , metadata: Nothing
        }
  
  -- 5. Add message and part to session state
  _ <- Operations.updateMessage assistantMessage ctx.sessionState
  _ <- Operations.updatePart (MessageV2Types.PartText textPart) ctx.sessionState
  
  pure $ Right unit
