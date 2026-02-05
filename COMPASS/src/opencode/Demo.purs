{-|
Module      : Opencode.Demo
Description : Integration demonstration
= COMPASS Integration Demo

Demonstrates the full flow from user input to LLM response with tool execution.

== Flow Overview

@
  User Input
      │
      ▼
  ┌─────────────────┐
  │ Provider        │  getLLMConfig(venice, model, apiKey)
  │ Registry        │
  └────────┬────────┘
           │ LLM.ProviderConfig
           ▼
  ┌─────────────────┐
  │ Session         │  createProcessor(config)
  │ Processor       │
  └────────┬────────┘
           │
           ▼
  ┌─────────────────┐
  │ Session.LLM     │  complete(providerConfig, request)
  │ (HTTP Client)   │
  └────────┬────────┘
           │
           ▼
  ┌─────────────────┐
  │ Venice AI       │  POST /chat/completions
  │ API             │
  └────────┬────────┘
           │
           ▼
  ┌─────────────────┐
  │ Tool Execution  │  If response has tool_calls
  │ (Bash, etc.)    │
  └────────┬────────┘
           │
           ▼
       Response
@

== Coeffect Tracking

@
  demo : Graded (Network ⊗ Terminal ⊗ FileSystem) Response
@

-}
module Opencode.Demo
  ( -- * Demo Functions
    runSimpleChat
  , runWithTools
    -- * Configuration
  , DemoConfig(..)
  , defaultDemoConfig
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff, launchAff_, runAff_)
import Effect.Console (log)
import Effect.Ref as Ref
import Effect.Class (liftEffect)
import Data.Array as Array

import Opencode.Session.LLM as LLM
import Opencode.Provider.Registry as Registry
import Opencode.Session.Processor as Processor
import Opencode.Types.Tool (ToolInfo, ToolContext, ToolResult)
import Data.Argonaut (encodeJson)

-- ════════════════════════════════════════════════════════════════════════════
-- CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

-- | Demo configuration
type DemoConfig =
  { provider :: String       -- Provider ID (e.g., "venice", "openai")
  , model :: String          -- Model ID (e.g., "llama-3.3-70b")
  , apiKey :: String         -- API key
  , userMessage :: String    -- User's input message
  }

-- | Default demo config using Venice
defaultDemoConfig :: DemoConfig
defaultDemoConfig =
  { provider: "venice"
  , model: "llama-3.3-70b"
  , apiKey: ""  -- Must be provided
  , userMessage: "What is 2 + 2?"
  }

-- ════════════════════════════════════════════════════════════════════════════
-- SIMPLE CHAT DEMO
-- ════════════════════════════════════════════════════════════════════════════

{-| Run a simple chat without tools.

This demonstrates the minimal path:
1. Create provider config from registry
2. Build LLM request with user message
3. Call LLM via HTTP
4. Return response
-}
runSimpleChat :: DemoConfig -> Aff (Either String String)
runSimpleChat config = do
  -- 1. Initialize provider registry
  registryRef <- liftEffect $ Ref.new Registry.initialState
  
  -- 2. Get LLM configuration from registry
  llmConfig <- liftEffect $ Registry.getLLMConfig 
    config.provider 
    config.model 
    config.apiKey 
    registryRef
  
  -- 3. Build LLM request
  let request =
        { model: config.model
        , messages: [LLM.userMessage config.userMessage]
        , temperature: Just 0.7
        , maxTokens: Just 1024
        , tools: Nothing
        , toolChoice: Nothing
        , stream: false
        }
  
  -- 4. Call LLM
  result <- LLM.complete llmConfig request
  
  -- 5. Extract response text
  pure $ case result of
    Left err -> Left err
    Right response -> 
      case Array.head response.choices of
        Nothing -> Left "No choices in response"
        Just choice -> 
          Right $ LLM.contentToString choice.message.content

-- ════════════════════════════════════════════════════════════════════════════
-- CHAT WITH TOOLS DEMO
-- ════════════════════════════════════════════════════════════════════════════

{-| Run a chat with tool support.

This demonstrates the full agent loop:
1. Create processor with tools
2. Send user message to LLM
3. If LLM requests tools, execute them
4. Return tool results to LLM
5. Repeat until completion
-}
runWithTools :: DemoConfig -> Array ToolInfo -> Aff (Either String String)
runWithTools config tools = do
  -- 1. Initialize provider registry
  registryRef <- liftEffect $ Ref.new Registry.initialState
  
  -- 2. Get LLM configuration
  llmConfig <- liftEffect $ Registry.getLLMConfig 
    config.provider 
    config.model 
    config.apiKey 
    registryRef
  
  -- 3. Create processor config
  let processorConfig =
        { sessionID: "demo-session"
        , model: config.model
        , agent: Nothing
        , maxIterations: 10
        , systemPrompt: Just "You are a helpful coding assistant. Use tools when needed."
        , providerConfig: llmConfig
        , tools: tools
        }
  
  -- 4. Validate and create processor
  case Processor.validateConfig processorConfig of
    Left err -> pure $ Left err
    Right validConfig -> do
      -- 5. Create runtime
      let runtime = Processor.createProcessor validConfig
      
      -- 6. Run single iteration (for demo)
      result <- Processor.processIteration runtime
      
      -- 7. Return result
      pure $ case result of
        Left err -> Left err
        Right state -> Right $ show state

-- ════════════════════════════════════════════════════════════════════════════
-- EXAMPLE TOOL DEFINITIONS
-- ════════════════════════════════════════════════════════════════════════════

-- | Example echo tool (for testing)
echoTool :: ToolInfo
echoTool =
  { id: "echo"
  , description: "Echo back the input message"
  , parameters: encodeJson
      { type: "object"
      , properties:
          { message: { type: "string", description: "Message to echo" }
          }
      , required: ["message"]
      }
  , execute: \args ctx -> pure
      { title: "Echo"
      , metadata: encodeJson {}
      , output: "Echo: (arguments received)"
      , attachments: Nothing
      }
  , formatValidationError: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
-- ENTRY POINT
-- ════════════════════════════════════════════════════════════════════════════

{-| Main entry point for demo.

Run from Node.js:
@
  const { runSimpleChat } = require('./output/Opencode.Demo')
  runSimpleChat({
    provider: 'venice',
    model: 'llama-3.3-70b',
    apiKey: process.env.VENICE_API_KEY,
    userMessage: 'Hello!'
  })()
    .then(result => console.log(result))
    .catch(err => console.error(err))
@
-}
main :: Effect Unit
main = launchAff_ do
  liftEffect $ log "COMPASS Demo - Simple Chat"
  liftEffect $ log "=========================="
  liftEffect $ log ""
  liftEffect $ log "This demo requires VENICE_API_KEY environment variable."
  liftEffect $ log "Run: export VENICE_API_KEY=your-key && node output/Opencode.Demo/index.js"
  pure unit
