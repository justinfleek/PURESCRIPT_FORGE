module Nexus.AgentOrchestrator.Launcher where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Maybe (fromMaybe)
import Nexus.AgentOrchestrator.Types (AgentType(..), AgentConfig, AgentStatus(..), AgentRecord, SandboxConfig)
import Nexus.AgentOrchestrator.Sandbox (createSandbox, launchInSandbox, Sandbox)
import Nexus.AgentOrchestrator.FFI (generateAgentIdFromSeed)

-- | Launch agent in sandbox (deterministic)
-- | Accepts explicit agentId for deterministic operation
-- | Returns agentId and processId on success
launchAgent :: AgentType -> AgentConfig -> Maybe SandboxConfig -> String -> Aff (Either String { agentId :: String, processId :: Int })
launchAgent agentType config sandboxConfig agentId = do
  -- Get sandbox config (use default if not provided)
  sandbox <- liftEffect $ createSandbox agentType agentId sandboxConfig
  
  -- Build command
  let command = buildAgentCommand agentType config
  
  -- Launch in sandbox
  result <- launchInSandbox sandbox command
  
  case result of
    Left err -> pure $ Left $ "Failed to launch agent: " <> err
    Right pid -> pure $ Right { agentId, processId: pid }

-- | Build agent command based on type
buildAgentCommand :: AgentType -> AgentConfig -> Array String
buildAgentCommand agentType config = case agentType of
  WebSearch ->
    [ "python3"
    , "-m", "nexus.web_search_agent"
    , "--query", fromMaybe "" config.initialQuery
    , "--max-results", show config.maxResults
    , "--timeout", show config.timeoutSeconds
    ]
  ContentExtraction ->
    [ "python3"
    , "-m", "nexus.content_extraction_agent"
    , "--timeout", show config.timeoutSeconds
    ]
  NetworkFormation ->
    [ "python3"
    , "-m", "nexus.network_formation_agent"
    , "--timeout", show config.timeoutSeconds
    ]
  DatabaseLayer ->
    [ "python3"
    , "-m", "nexus.database_layer"
    ]

