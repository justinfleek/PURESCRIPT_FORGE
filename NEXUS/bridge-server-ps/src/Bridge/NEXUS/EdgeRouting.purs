-- | Bridge Server NEXUS - Edge Routing
-- | Routes requests to agents in the closest Fly.io region
module Bridge.NEXUS.EdgeRouting where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff, makeAff, nonCanceler)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Argonaut (Json, encodeJson, decodeJson, jsonParser, class DecodeJson, class EncodeJson)
import Data.Argonaut.Core as AC (stringify)
import Data.Argonaut.Decode (class DecodeJson, (.:), (.:?))
import Bridge.NEXUS.Types (AgentLaunchResponse, AgentStatusResponse)

-- | User location (from HTTP headers or explicit)
type UserLocation =
  { lat :: Maybe Number
  , lon :: Maybe Number
  , country :: Maybe String
  , city :: Maybe String
  , ipAddress :: Maybe String
  }

-- | Fly.io region code
type RegionCode = String

-- | Available Fly.io regions
type RegionInfo =
  { code :: RegionCode
  , city :: String
  , country :: String
  , lat :: Number
  , lon :: Number
  }

-- | Agent request to route
type AgentRequest =
  { method :: String
  , params :: Json
  , agentId :: Maybe String
  }

-- | Agent response from edge region
type AgentResponse =
  { success :: Boolean
  , data :: Json
  , region :: RegionCode
  , latencyMs :: Number
  }

-- | Foreign imports for region detection and routing
foreign import detectUserLocationFromHeaders_ :: Effect (Maybe UserLocation)
foreign import findClosestRegion_ :: UserLocation -> Effect (Maybe RegionInfo)
foreign import callAgentInRegion_ :: RegionCode -> AgentRequest -> Aff (Either String AgentResponse)
foreign import launchAgentInRegion_ :: RegionCode -> String -> String -> Aff (Either String AgentLaunchResponse)

-- | Detect user location from headers
detectUserLocationFromHeaders :: Effect (Maybe UserLocation)
detectUserLocationFromHeaders = detectUserLocationFromHeaders_

-- | Find closest region to user location
findClosestRegion :: UserLocation -> Effect (Maybe RegionInfo)
findClosestRegion = findClosestRegion_

-- | Call agent in specific region
callAgentInRegion :: RegionCode -> AgentRequest -> Aff (Either String AgentResponse)
callAgentInRegion = callAgentInRegion_

-- | Launch agent in specific region
launchAgentInRegion :: RegionCode -> String -> String -> Aff (Either String AgentLaunchResponse)
launchAgentInRegion = launchAgentInRegion_

-- | Route agent request to closest region
routeToEdgeAgent :: UserLocation -> AgentRequest -> Aff (Either String AgentResponse)
routeToEdgeAgent userLoc request = do
  -- Find closest region
  closestRegionResult <- makeAff \callback -> do
    regionInfo <- findClosestRegion userLoc
    case regionInfo of
      Just info -> callback $ Right info
      Nothing -> callback $ Left "Failed to find closest region"
    pure nonCanceler
  
  case closestRegionResult of
    Left err -> pure $ Left err
    Right regionInfo -> do
      -- Forward request to agent in closest region
      callAgentInRegion regionInfo.code request

-- | Launch agent in closest region
launchEdgeAgent :: UserLocation -> String -> String -> Aff (Either String AgentLaunchResponse)
launchEdgeAgent userLoc agentType config = do
  -- Find closest region
  closestRegionResult <- makeAff \callback -> do
    regionInfo <- findClosestRegion userLoc
    case regionInfo of
      Just info -> callback $ Right info
      Nothing -> callback $ Left "Failed to find closest region"
    pure nonCanceler
  
  case closestRegionResult of
    Left err -> pure $ Left err
    Right regionInfo -> do
      -- Launch agent in closest region
      launchAgentInRegion regionInfo.code agentType config

-- | Get agent status from edge region
getEdgeAgentStatus :: UserLocation -> String -> Aff (Either String AgentStatusResponse)
getEdgeAgentStatus userLoc agentId = do
  -- Find closest region
  closestRegionResult <- makeAff \callback -> do
    regionInfo <- findClosestRegion userLoc
    case regionInfo of
      Just info -> callback $ Right info
      Nothing -> callback $ Left "Failed to find closest region"
    pure nonCanceler
  
  case closestRegionResult of
    Left err -> pure $ Left err
    Right regionInfo -> do
      -- Create agent request
      let request = { method: "nexus.agent.status", params: encodeJson { agentId }, agentId: Just agentId }
      -- Call agent in closest region
      response <- callAgentInRegion regionInfo.code request
      case response of
        Left err -> pure $ Left err
        Right agentResp -> do
          -- Parse AgentStatusResponse from response data
          case decodeJson agentResp.data of
            Left _ -> pure $ Left "Failed to parse agent status"
            Right statusResp -> pure $ Right statusResp

-- | Calculate distance between two coordinates (Haversine formula)
-- | Returns distance in kilometers
calculateDistance :: Number -> Number -> Number -> Number -> Number
calculateDistance lat1 lon1 lat2 lon2 =
  let
    earthRadius = 6371.0  -- Earth radius in kilometers
    dLat = degToRad (lat2 - lat1)
    dLon = degToRad (lon2 - lon1)
    a = sin (dLat / 2.0) * sin (dLat / 2.0) +
        cos (degToRad lat1) * cos (degToRad lat2) *
        sin (dLon / 2.0) * sin (dLon / 2.0)
    c = 2.0 * atan2 (sqrt a) (sqrt (1.0 - a))
  in
    earthRadius * c

degToRad :: Number -> Number
degToRad deg = deg * 3.141592653589793 / 180.0

-- | Available Fly.io regions
availableRegions :: Array RegionInfo
availableRegions =
  [ { code: "ord", city: "Chicago", country: "United States", lat: 41.8781, lon: (-87.6298) }
  , { code: "sjc", city: "San Jose", country: "United States", lat: 37.3382, lon: (-121.8863) }
  , { code: "lhr", city: "London", country: "United Kingdom", lat: 51.5074, lon: (-0.1278) }
  , { code: "nrt", city: "Tokyo", country: "Japan", lat: 35.6762, lon: 139.6503 }
  , { code: "iad", city: "Washington DC", country: "United States", lat: 38.9072, lon: (-77.0369) }
  , { code: "fra", city: "Frankfurt", country: "Germany", lat: 50.1109, lon: 8.6821 }
  , { code: "sin", city: "Singapore", country: "Singapore", lat: 1.3521, lon: 103.8198 }
  , { code: "syd", city: "Sydney", country: "Australia", lat: (-33.8688), lon: 151.2093 }
  , { code: "gru", city: "São Paulo", country: "Brazil", lat: (-23.5505), lon: (-46.6333) }
  , { code: "yyz", city: "Toronto", country: "Canada", lat: 43.6532, lon: (-79.3832) }
  ]
