-- | Nexus Agent Orchestrator - Region Detection and Routing
-- | Determines closest Fly.io region based on user location
module Nexus.AgentOrchestrator.Region where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Control.Monad (guard)
import Prelude hiding (sin, cos, atan2, sqrt, pi)
import qualified Prelude as P

-- | Fly.io region codes and their locations
data FlyIORegion = ORD | SJC | LHR | NRT | IAD | FRA | SIN | SYD | GRU | YYZ
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Region metadata: code, city, country, coordinates (lat, lon)
data RegionInfo = RegionInfo
  { regionCode :: Text
  , regionCity :: Text
  , regionCountry :: Text
  , regionLat :: Double
  , regionLon :: Double
  }
  deriving (Eq, Show)

-- | User location (IP-based or explicit)
data UserLocation = UserLocation
  { userLat :: Double
  , userLon :: Double
  , userCountry :: Maybe Text
  , userCity :: Maybe Text
  }
  deriving (Eq, Show)

-- | Fly.io region registry with coordinates
flyIORegions :: Map FlyIORegion RegionInfo
flyIORegions = Map.fromList
  [ (ORD, RegionInfo "ord" "Chicago" "United States" 41.8781 (-87.6298))
  , (SJC, RegionInfo "sjc" "San Jose" "United States" 37.3382 (-121.8863))
  , (LHR, RegionInfo "lhr" "London" "United Kingdom" 51.5074 (-0.1278))
  , (NRT, RegionInfo "nrt" "Tokyo" "Japan" 35.6762 139.6503)
  , (IAD, RegionInfo "iad" "Washington DC" "United States" 38.9072 (-77.0369))
  , (FRA, RegionInfo "fra" "Frankfurt" "Germany" 50.1109 8.6821)
  , (SIN, RegionInfo "sin" "Singapore" "Singapore" 1.3521 103.8198)
  , (SYD, RegionInfo "syd" "Sydney" "Australia" (-33.8688) 151.2093)
  , (GRU, RegionInfo "gru" "São Paulo" "Brazil" (-23.5505) (-46.6333))
  , (YYZ, RegionInfo "yyz" "Toronto" "Canada" 43.6532 (-79.3832))
  ]

-- | Calculate great-circle distance (Haversine formula) in kilometers
haversineDistance :: Double -> Double -> Double -> Double -> Double
haversineDistance lat1 lon1 lat2 lon2 =
  let
    earthRadius = 6371.0  -- Earth radius in kilometers
    dLat = degToRad (lat2 - lat1)
    dLon = degToRad (lon2 - lon1)
    a = P.sin (dLat / 2) * P.sin (dLat / 2) +
        P.cos (degToRad lat1) * P.cos (degToRad lat2) *
        P.sin (dLon / 2) * P.sin (dLon / 2)
    c = 2 * P.atan2 (P.sqrt a) (P.sqrt (1 - a))
  in
    earthRadius * c

degToRad :: Double -> Double
degToRad deg = deg * P.pi / 180.0

-- | Find closest Fly.io region to user location
findClosestRegion :: UserLocation -> Maybe (FlyIORegion, RegionInfo, Double)
findClosestRegion userLoc =
  let
    distances = Map.mapMaybe (\regionInfo ->
      let dist = haversineDistance
            (userLat userLoc)
            (userLon userLoc)
            (regionLat regionInfo)
            (regionLon regionInfo)
      in Just (regionInfo, dist)
    ) flyIORegions
    
    -- Find minimum distance
    minDist = if Map.null distances
      then Nothing
      else Just $ snd $ Map.foldlWithKey (\acc@(_, minDist) region (info, dist) ->
        if dist < minDist then (region, dist) else acc
      ) (ORD, 999999.0) distances
    
  in case minDist of
    Nothing -> Nothing
    Just dist -> do
      let (closestRegion, _) = Map.foldlWithKey (\acc@(bestRegion, bestDist) region (info, d) ->
        if d < bestDist then (region, d) else acc
      ) (ORD, 999999.0) distances
      regionInfo <- Map.lookup closestRegion flyIORegions
      pure (closestRegion, regionInfo, dist)

-- | Get region code as Text
regionCodeText :: FlyIORegion -> Text
regionCodeText region = case Map.lookup region flyIORegions of
  Just info -> regionCode info
  Nothing -> T.pack $ show region

-- | Parse region code from Text
parseRegionCode :: Text -> Maybe FlyIORegion
parseRegionCode code = Map.foldlWithKey (\acc region info ->
  if regionCode info == T.toLower code then Just region else acc
) Nothing flyIORegions

-- | Get all available regions
allRegions :: [RegionInfo]
allRegions = Map.elems flyIORegions

-- | Detect user location from IP address (placeholder - would use IP geolocation API)
detectUserLocationFromIP :: Text -> IO (Maybe UserLocation)
detectUserLocationFromIP ipAddress = do
  -- In production, would call IP geolocation service (e.g., ipapi.co, ip-api.com)
  -- For now, return Nothing (will use default region)
  pure Nothing

-- | Detect user location from HTTP headers (X-Forwarded-For, CF-IPCountry, etc.)
detectUserLocationFromHeaders :: Map Text Text -> Maybe UserLocation
detectUserLocationFromHeaders headers =
  -- Check Cloudflare headers
  case Map.Map.lookup "cf-ipcountry" headers of
    Just country -> do
      -- Use country-based default coordinates
      let (lat, lon) = countryDefaultCoords country
      pure $ UserLocation lat lon (Just country) Nothing
    Nothing ->
      -- Check Fly.io region header
      case Map.Map.lookup "fly-region" headers of
        Just regionCode -> do
          region <- parseRegionCode regionCode
          info <- Map.lookup region flyIORegions
          pure $ UserLocation (regionLat info) (regionLon info) (Just $ regionCountry info) (Just $ regionCity info)
        Nothing -> Nothing

-- | Default coordinates for countries (major cities)
countryDefaultCoords :: Text -> (Double, Double)
countryDefaultCoords country = case T.toUpper country of
  "US" -> (39.8283, (-98.5795))  -- Geographic center of US
  "GB" -> (51.5074, (-0.1278))  -- London
  "JP" -> (35.6762, 139.6503)    -- Tokyo
  "DE" -> (50.1109, 8.6821)      -- Frankfurt
  "SG" -> (1.3521, 103.8198)     -- Singapore
  "AU" -> (-33.8688, 151.2093)   -- Sydney
  "BR" -> (-23.5505, (-46.6333)) -- São Paulo
  "CA" -> (43.6532, (-79.3832))  -- Toronto
  _ -> (0.0, 0.0)  -- Default to equator/prime meridian
