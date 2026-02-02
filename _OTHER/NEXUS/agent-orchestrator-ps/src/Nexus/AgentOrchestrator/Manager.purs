module Nexus.AgentOrchestrator.Manager where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Nexus.AgentOrchestrator.Types (AgentType, AgentConfig, AgentStatus(..), AgentRecord)
import Nexus.AgentOrchestrator.Launcher (launchAgent)
import Nexus.AgentOrchestrator.FFI (callBubblewrap, generateAgentIdFromSeed, formatTimestamp, killProcess)
import Data.Maybe (Maybe(..))

-- | Agent manager state (mutable reference)
type AgentManagerState = Ref.Ref (Map.Map String AgentRecord)

-- | Initialize agent manager
initAgentManager :: Effect AgentManagerState
initAgentManager = do
  Ref.new Map.empty

-- | Start agent (deterministic)
-- | Accepts explicit time (milliseconds since epoch) and seed for deterministic ID generation
startAgent :: AgentManagerState -> AgentType -> AgentConfig -> Number -> Int -> Aff (Either String String)
startAgent state agentType config timestampMs seed = do
  -- Generate deterministic agent ID from seed
  let agentId = generateAgentIdFromSeed "nexus-agent" seed
  
  -- Format timestamp deterministically
  let timestamp = formatTimestamp timestampMs
  
  -- Launch agent
  result <- launchAgent agentType config Nothing agentId
  
  case result of
    Left err -> pure $ Left err
    Right { processId } -> do
      -- Create agent record
      let agentRecord = 
            { agentId
            , agentType
            , config
            , status: Running
            , startedAt: timestamp
            , updatedAt: timestamp
            , processId: Just processId
            }
      
      -- Store agent in state
      liftEffect $ Ref.modify_ (Map.insert agentId agentRecord) state
      
      pure $ Right agentId

-- | Stop agent (deterministic)
-- | Accepts explicit time (milliseconds since epoch) for deterministic updates
stopAgent :: AgentManagerState -> String -> Number -> Aff (Either String Unit)
stopAgent state agentId timestampMs = do
  -- Get current state
  agents <- liftEffect $ Ref.read state
  
  -- Check if agent exists
  case Map.lookup agentId agents of
    Nothing -> pure $ Left $ "Agent not found: " <> agentId
    Just agentRecord -> do
      -- Format timestamp deterministically
      let timestamp = formatTimestamp timestampMs
      
      -- Update agent status
      let updatedRecord = agentRecord { status = Stopped, updatedAt = timestamp }
      
      -- Update state
      liftEffect $ Ref.modify_ (Map.insert agentId updatedRecord) state
      
      -- Kill agent process if PID is available
      case agentRecord.processId of
        Just pid -> do
          result <- liftEffect $ killProcess pid
          case result of
            Left err -> pure $ Left $ "Failed to kill process: " <> err
            Right _ -> pure $ Right unit
        Nothing -> pure $ Right unit

-- | Get agent status
getAgentStatus :: AgentManagerState -> String -> Effect (Maybe AgentRecord)
getAgentStatus state agentId = do
  agents <- Ref.read state
  pure $ Map.lookup agentId agents

-- | List all agents
listAgents :: AgentManagerState -> Effect (Array AgentRecord)
listAgents state = do
  agents <- Ref.read state
  pure $ Map.values agents

-- | List agents by type
listAgentsByType :: AgentManagerState -> AgentType -> Effect (Array AgentRecord)
listAgentsByType state agentType = do
  allAgents <- listAgents state
  pure $ Array.filter (\a -> a.agentType == agentType) allAgents

-- | List agents by status
listAgentsByStatus :: AgentManagerState -> AgentStatus -> Effect (Array AgentRecord)
listAgentsByStatus state status = do
  allAgents <- listAgents state
  pure $ Array.filter (\a -> a.status == status) allAgents
