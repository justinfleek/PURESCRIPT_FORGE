-- | Forge Sidepanel Plugin
-- | PureScript implementation that compiles to JavaScript for Forge
-- | Spec: 21-PLUGIN-SYSTEM
module Forge.Plugin.Main where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Bridge.FFI.Forge.Plugin (PluginInput, Hooks, Event)
import Bridge.FFI.WebSocket.Client (BridgeClient, createClient, connect, sendEvent, sendMessage, sendToolExecution, sendConfig)

import Effect.Class (liftEffect)

-- | FFI functions
foreign import getBridgeUrl :: Aff String
foreign import logError :: String -> Aff Unit
foreign import logInfo :: String -> Aff Unit
foreign import emptyHooks :: Hooks
foreign import createHooks :: BridgeClient -> Hooks
foreign import handleEvent :: BridgeClient -> { event :: Event } -> Aff Unit
foreign import handleChatMessage :: BridgeClient -> { sessionID :: String, messageID :: Maybe String, agent :: Maybe String, model :: Maybe { providerID :: String, modelID :: String }, message :: String, parts :: Array String } -> Aff Unit
foreign import handleToolExecuteAfter :: BridgeClient -> { tool :: String, sessionID :: String, callID :: String, title :: String, output :: String, metadata :: String } -> Aff Unit
foreign import handleConfig :: BridgeClient -> String -> Aff Unit

-- | Plugin entry point (exported for Forge)
sidepanelPlugin :: PluginInput -> Aff Hooks
sidepanelPlugin input = do
  -- Get bridge server URL
  bridgeUrl <- getBridgeUrl
  
  -- Create bridge client
  client <- liftEffect $ createClient bridgeUrl
  
  -- Connect to bridge server
  result <- connect client
  case result of
    Left err -> do
      -- Log error but return no-op hooks (graceful degradation)
      logError ("Failed to connect to Bridge Server: " <> err)
      pure emptyHooks
    Right _ -> do
      logInfo ("Connected to Bridge Server: " <> bridgeUrl)
      pure (createHooks client)
