-- | Nexus Edge Orchestrator CLI
-- | Command-line interface for edge-aware agent deployment
module Main where

import Options.Applicative
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString as BS
import System.Environment (getEnv, lookupEnv)
import Control.Exception (try, IOException)
import System.Exit (exitFailure, exitSuccess)

import Nexus.AgentOrchestrator.Edge
  ( AgentConfig(..)
  , AgentLaunchResult(..)
  , UserLocation(..)
  , launchEdgeAgent
  , launchEdgeAgentFromHeaders
  , getEdgeAgentStatus
  , defaultAgentConfig
  , agentTypeToImage
  )
import Nexus.AgentOrchestrator.Region (allRegions, RegionInfo(..))
import Nexus.AgentOrchestrator.FlyIO (MachineResponse(..))

-- | CLI commands
data Command
  = Launch
    { launchAgentType :: Text
    , launchLat :: Maybe Double
    , launchLon :: Maybe Double
    , launchCountry :: Maybe Text
    , launchConfig :: Maybe Text
    }
  | Status
    { statusMachineId :: Text
    }
  | ListRegions

-- | Launch command parser
launchParser :: Parser Command
launchParser = Launch
  <$> strOption
    ( long "agent-type"
    <> short 't'
    <> help "Agent type (web_search, content_extraction, network_formation)"
    <> metavar "TYPE"
    )
  <*> optional (option auto
    ( long "lat"
    <> help "User latitude"
    <> metavar "LAT"
    ))
  <*> optional (option auto
    ( long "lon"
    <> help "User longitude"
    <> metavar "LON"
    ))
  <*> optional (strOption
    ( long "country"
    <> help "User country code"
    <> metavar "COUNTRY"
    ))
  <*> optional (strOption
    ( long "config"
    <> short 'c'
    <> help "Agent configuration JSON"
    <> metavar "CONFIG"
    ))
  <*> optional (strOption
    ( long "region"
    <> help "Fly.io region code (overrides location-based selection)"
    <> metavar "REGION"
    ))

-- | Status command parser
statusParser :: Parser Command
statusParser = Status
  <$> strArgument
    ( help "Machine ID"
    <> metavar "MACHINE_ID"
    )

-- | List regions command parser
listRegionsParser :: Parser Command
listRegionsParser = pure ListRegions

-- | Main command parser
commandParser :: Parser Command
commandParser = subparser
  ( command "launch" (info launchParser (progDesc "Launch agent on edge machine"))
  <> command "status" (info statusParser (progDesc "Get agent status"))
  <> command "list-regions" (info listRegionsParser (progDesc "List available Fly.io regions"))
  )

-- | Main function
main :: IO ()
main = do
  cmd <- execParser (info commandParser (fullDesc <> progDesc "Nexus Edge Orchestrator CLI"))
  
  case cmd of
    Launch agentType mLat mLon mCountry mConfig launchRegion -> do
      -- Parse agent configuration
      let baseConfig = defaultAgentConfig agentType
      let agentConfig = case mConfig of
            Just configJson -> case Aeson.eitherDecode (BL.fromStrict $ T.encodeUtf8 $ T.pack configJson) of
              Right cfg -> cfg
              Left _ -> baseConfig { agentImage = agentTypeToImage agentType }
            Nothing -> baseConfig { agentImage = agentTypeToImage agentType }
      
      -- Determine user location or use explicit region
      result <- case launchRegion of
        Just regionCode -> do
          -- Use explicit region (would need to parse region code and create UserLocation)
          -- For now, use default location
          let userLoc = UserLocation 0.0 0.0 mCountry Nothing
          launchEdgeAgent userLoc agentConfig
        Nothing -> do
          -- Use location-based region selection
          let userLoc = case (mLat, mLon) of
                (Just lat, Just lon) -> UserLocation lat lon mCountry Nothing
                _ -> UserLocation 0.0 0.0 mCountry Nothing  -- Default if no coordinates
          launchEdgeAgent userLoc agentConfig
      case result of
        Left err -> do
          TIO.putStrLn $ T.pack $ "Error: " ++ err
          exitFailure
        Right launchResult -> do
          let json = Aeson.encode launchResult
          BL.putStrLn json
    
    Status machineId -> do
      result <- getEdgeAgentStatus (T.pack machineId)
      case result of
        Left err -> do
          TIO.putStrLn $ T.pack $ "Error: " ++ err
          exitFailure
        Right machineResp -> do
          let json = Aeson.encode machineResp
          BL.putStrLn json
    
    ListRegions -> do
      let regions = allRegions
      let json = Aeson.encode regions
      BL.putStrLn json
