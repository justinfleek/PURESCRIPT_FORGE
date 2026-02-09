-- | Nexus Agent Orchestrator - Edge-Aware Agent Launcher
-- | Launches agents on Fly.io machines in the region closest to the user
module Nexus.AgentOrchestrator.Edge where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Aeson (ToJSON(..), FromJSON(..), object, (.=), (.:), (.:?))
import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Lazy as BL
import Data.Maybe (Maybe(..))
import Control.Monad (guard)
import System.Environment (getEnv, lookupEnv)
import Control.Exception (try, IOException)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Nexus.AgentOrchestrator.Region
  ( UserLocation(..)
  , FlyIORegion
  , findClosestRegion
  , detectUserLocationFromHeaders
  , regionCodeText
  )
import Nexus.AgentOrchestrator.FlyIO
  ( FlyIOConfig(..)
  , MachineConfig(..)
  , MachineResponse(..)
  , getFlyIOConfig
  , createMachine
  , startMachine
  , getMachine
  )

-- | Agent configuration for edge deployment
data AgentConfig = AgentConfig
  { agentType :: Text
  , agentImage :: Text  -- Docker image for agent
  , agentEnv :: [(Text, Text)]  -- Environment variables
  , agentSize :: Text  -- Machine size (e.g., "shared-cpu-1x")
  }
  deriving (Eq, Show)

instance ToJSON AgentConfig where
  toJSON config = object
    [ "type" .= agentType config
    , "image" .= agentImage config
    , "env" .= object (map (\(k, v) -> T.unpack k .= v) (agentEnv config))
    , "size" .= agentSize config
    ]

instance FromJSON AgentConfig where
  parseJSON = Aeson.withObject "AgentConfig" $ \o -> do
    agentType <- o .: "type"
    agentImage <- o .: "image"
    envObj <- o .:? "env"
    agentSize <- o .: "size"
    -- Parse env object into list (if present)
    let agentEnv = case envObj of
          Just (Aeson.Object envMap) -> map (\(k, v) -> (T.pack k, T.pack $ Aeson.encode v)) $ Aeson.toKeyValue envMap
          _ -> []
    pure $ AgentConfig agentType agentImage agentEnv agentSize

-- | Agent launch result
data AgentLaunchResult = AgentLaunchResult
  { launchAgentId :: Text
  , launchMachineId :: Text
  , launchRegion :: FlyIORegion
  , launchRegionCode :: Text
  , launchDistance :: Double  -- Distance in km to user
  }
  deriving (Eq, Show)

instance ToJSON AgentLaunchResult where
  toJSON result = object
    [ "agentId" .= launchAgentId result
    , "machineId" .= launchMachineId result
    , "region" .= regionCodeText (launchRegion result)
    , "regionCode" .= launchRegionCode result
    , "distanceKm" .= launchDistance result
    ]

-- | Launch agent on edge machine closest to user
launchEdgeAgent :: UserLocation -> AgentConfig -> IO (Either String AgentLaunchResult)
launchEdgeAgent userLoc agentConfig = do
  -- Find closest Fly.io region
  case findClosestRegion userLoc of
    Nothing -> pure $ Left "Failed to find closest region"
    Just (closestRegion, regionInfo, distance) -> do
      -- Get Fly.io configuration
      flyConfigResult <- getFlyIOConfig
      case flyConfigResult of
        Left err -> pure $ Left $ "Fly.io config error: " ++ err
        Right flyConfig -> do
          -- Get database URL from environment
          mDatabaseUrl <- lookupEnv "DATABASE_URL"
          let databaseUrl = case mDatabaseUrl of
                Just url -> T.pack url
                Nothing -> T.pack "postgresql://localhost/nexus"
          
          -- Build machine configuration
          let regionCode = regionCodeText closestRegion
          let machineConfig = MachineConfig
                { machineImage = agentImage agentConfig
                , machineRegion = closestRegion
                , machineEnv = ("DATABASE_URL", databaseUrl)
                          : ("REGION", regionCode)
                          : ("AGENT_TYPE", agentType agentConfig)
                          : agentEnv agentConfig
                , machineSize = agentSize agentConfig
                , machineVolumes = []
                }
          
          -- Create machine in closest region
          createResult <- createMachine flyConfig machineConfig
          case createResult of
            Left err -> pure $ Left $ "Failed to create machine: " ++ err
            Right machineResp -> do
              -- Start the machine
              startResult <- startMachine flyConfig (machineId machineResp)
              case startResult of
                Left err -> pure $ Left $ "Failed to start machine: " ++ err
                Right _ -> do
                  -- Generate agent ID (would use proper ID generation in production)
                  let agentId = T.pack $ "agent-" ++ T.unpack (machineId machineResp)
                  
                  pure $ Right $ AgentLaunchResult
                    { launchAgentId = agentId
                    , launchMachineId = machineId machineResp
                    , launchRegion = closestRegion
                    , launchRegionCode = regionCode
                    , launchDistance = distance
                    }

-- | Launch agent with automatic region detection from headers
launchEdgeAgentFromHeaders :: [(Text, Text)] -> AgentConfig -> IO (Either String AgentLaunchResult)
launchEdgeAgentFromHeaders headers agentConfig = do
  let headersMap = Map.fromList headers
  case detectUserLocationFromHeaders headersMap of
    Nothing -> do
      -- Fallback to default region (ORD - Chicago)
      let defaultLoc = UserLocation 41.8781 (-87.6298) (Just $ T.pack "US") (Just $ T.pack "Chicago")
      launchEdgeAgent defaultLoc agentConfig
    Just userLoc -> launchEdgeAgent userLoc agentConfig

-- | Get agent status by machine ID
getEdgeAgentStatus :: Text -> IO (Either String MachineResponse)
getEdgeAgentStatus machineId = do
  flyConfigResult <- getFlyIOConfig
  case flyConfigResult of
    Left err -> pure $ Left $ "Fly.io config error: " ++ err
    Right flyConfig -> getMachine flyConfig machineId

-- | Default agent configuration for common agent types
defaultAgentConfig :: Text -> AgentConfig
defaultAgentConfig agentType = AgentConfig
  { agentType = agentType
  , agentImage = T.pack "nexus-agent:latest"
  , agentEnv = []
  , agentSize = T.pack "shared-cpu-1x"
  }

-- | Agent type to Docker image mapping
agentTypeToImage :: Text -> Text
agentTypeToImage agentType = case T.toLower agentType of
  "web_search" -> T.pack "nexus-web-search-agent:latest"
  "content_extraction" -> T.pack "nexus-content-extraction-agent:latest"
  "network_formation" -> T.pack "nexus-network-formation-agent:latest"
  _ -> T.pack "nexus-agent:latest"
