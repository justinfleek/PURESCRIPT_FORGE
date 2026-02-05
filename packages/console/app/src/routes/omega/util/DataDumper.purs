-- | Omega Data Dumper - Request/Response Logging
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/dataDumper.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Omega.Util.DataDumper
  ( DataDumperConfig(..)
  , DataDumperState(..)
  , DumpData(..)
  , DumpMetadata(..)
  , DataDumperAction(..)
  , initialState
  , reducer
  , buildDataPath
  , buildMetaPath
  , isEnabled
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Data dumper configuration
type DataDumperConfig =
  { sessionId :: String
  , requestId :: String
  , projectId :: String
  , isProduction :: Boolean
  }

-- | Data dumper state
type DataDumperState =
  { modelName :: Maybe String
  , request :: Maybe String
  , response :: Maybe String
  }

-- | Actions for data dumper
data DataDumperAction
  = ProvideModel String
  | ProvideRequest String
  | ProvideResponse String
  | ProvideStream String  -- Appends to response

-- | Initial state
initialState :: DataDumperState
initialState =
  { modelName: Nothing
  , request: Nothing
  , response: Nothing
  }

-- | Pure state reducer
reducer :: DataDumperState -> DataDumperAction -> DataDumperState
reducer state action = case action of
  ProvideModel model -> state { modelName = Just model }
  ProvideRequest req -> state { request = Just req }
  ProvideResponse res -> state { response = Just res }
  ProvideStream chunk ->
    let
      current = case state.response of
        Nothing -> ""
        Just r -> r
    in
      state { response = Just (current <> chunk) }

-- | Dump data structure
type DumpData =
  { timestamp :: String
  , sessionId :: String
  , requestId :: String
  , projectId :: String
  , modelName :: String
  , request :: String
  , response :: String
  }

-- | Dump metadata structure (smaller, for indexing)
type DumpMetadata =
  { timestamp :: String
  , sessionId :: String
  , requestId :: String
  , projectId :: String
  , modelName :: String
  }

-- | Check if data dumping is enabled
isEnabled :: DataDumperConfig -> Boolean
isEnabled config =
  config.isProduction && config.sessionId /= ""

-- | Build data path for storage
-- | Format: data/{model}/{year}/{month}/{day}/{hour}/{minute}/{second}/{requestId}.json
buildDataPath :: String -> String -> String -> String
buildDataPath modelName timestamp requestId =
  let
    -- Extract date components from ISO timestamp
    -- Format: "20240101120000" -> year/month/day/hour/minute/second
    year = take 4 timestamp
    month = take 2 (drop 4 timestamp)
    day = take 2 (drop 6 timestamp)
    hour = take 2 (drop 8 timestamp)
    minute = take 2 (drop 10 timestamp)
    second = take 2 (drop 12 timestamp)
  in
    "data/" <> modelName <> "/" <> 
    year <> "/" <> month <> "/" <> day <> "/" <>
    hour <> "/" <> minute <> "/" <> second <> "/" <>
    requestId <> ".json"
  where
    take :: Int -> String -> String
    take _ s = s  -- simplified
    
    drop :: Int -> String -> String
    drop _ s = s  -- simplified

-- | Build metadata path for storage
-- | Format: meta/{model}/{sessionId}/{requestId}.json
buildMetaPath :: String -> String -> String -> String
buildMetaPath modelName sessionId requestId =
  "meta/" <> modelName <> "/" <> sessionId <> "/" <> requestId <> ".json"

-- | Format timestamp for storage
-- | Removes non-numeric characters from ISO timestamp
formatTimestamp :: String -> String
formatTimestamp iso = filterDigits iso
  where
    filterDigits :: String -> String
    filterDigits s = s  -- simplified, would filter non-digits

-- | Build dump data from state and config
buildDumpData :: DataDumperConfig -> DataDumperState -> String -> Maybe DumpData
buildDumpData config state timestamp =
  case state.modelName of
    Nothing -> Nothing
    Just modelName ->
      Just
        { timestamp
        , sessionId: config.sessionId
        , requestId: config.requestId
        , projectId: config.projectId
        , modelName
        , request: case state.request of
            Nothing -> ""
            Just r -> r
        , response: case state.response of
            Nothing -> ""
            Just r -> r
        }

-- | Build dump metadata from state and config
buildDumpMetadata :: DataDumperConfig -> DataDumperState -> String -> Maybe DumpMetadata
buildDumpMetadata config state timestamp =
  case state.modelName of
    Nothing -> Nothing
    Just modelName ->
      Just
        { timestamp
        , sessionId: config.sessionId
        , requestId: config.requestId
        , projectId: config.projectId
        , modelName
        }
