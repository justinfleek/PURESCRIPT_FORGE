-- | Nexus Agent Orchestrator - Fly.io Machine API Integration
-- | Manages agent deployment and lifecycle on Fly.io machines
module Nexus.AgentOrchestrator.FlyIO where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Aeson (ToJSON(..), FromJSON(..), object, (.=), (.:), (.:?))
import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Lazy as BL
import Data.Maybe (Maybe(..))
import Control.Monad (guard)
import Network.HTTP.Simple
  ( httpJSON
  , httpLBS
  , setRequestMethod
  , setRequestHeader
  , setRequestBodyLBS
  , parseRequest_
  , getResponseBody
  , getResponseStatus
  )
import Network.HTTP.Types (status200, status201, status404)
import qualified Network.HTTP.Types.Status as Status
import System.Environment (getEnv, lookupEnv)
import Control.Exception (try, IOException)

import Nexus.AgentOrchestrator.Region (FlyIORegion, regionCodeText)

-- | Fly.io Machine API configuration
data FlyIOConfig = FlyIOConfig
  { flyIOApiToken :: Text
  , flyIOAppName :: Text
  , flyIOApiBase :: Text  -- e.g., "https://api.machines.dev/v1"
  }
  deriving (Eq, Show)

-- | Machine configuration for agent deployment
data MachineConfig = MachineConfig
  { machineImage :: Text
  , machineRegion :: FlyIORegion
  , machineEnv :: [(Text, Text)]
  , machineSize :: Text  -- e.g., "shared-cpu-1x", "shared-cpu-2x"
  , machineVolumes :: [Text]
  }
  deriving (Eq, Show)

instance ToJSON MachineConfig where
  toJSON config = object
    [ "region" .= regionCodeText (machineRegion config)
    , "config" .= object
        [ "image" .= machineImage config
        , "env" .= object (map (\(k, v) -> T.unpack k .= v) (machineEnv config))
        , "guest" .= object
            [ "cpu_kind" .= ("shared" :: String)
            , "cpus" .= (1 :: Int)
            , "memory_mb" .= (256 :: Int)
            ]
        , "init" .= object []
        ]
    ]

-- | Machine state
data MachineState = MachineStateStarting | MachineStateStarted | MachineStateStopped | MachineStateDestroyed
  deriving (Eq, Show)

instance ToJSON MachineState where
  toJSON = Aeson.String . T.pack . show

instance FromJSON MachineState where
  parseJSON = Aeson.withText "MachineState" $ \t -> case T.toLower t of
    "starting" -> pure MachineStateStarting
    "started" -> pure MachineStateStarted
    "stopped" -> pure MachineStateStopped
    "destroyed" -> pure MachineStateDestroyed
    _ -> fail $ "Unknown machine state: " ++ T.unpack t

-- | Fly.io Machine response
data MachineResponse = MachineResponse
  { machineId :: Text
  , machineState :: MachineState
  , machineRegion :: Text
  , machineImage :: Text
  , machineCreatedAt :: Text
  }
  deriving (Eq, Show)

instance FromJSON MachineResponse where
  parseJSON = Aeson.withObject "MachineResponse" $ \o -> do
    machineId <- o .: "id"
    machineState <- o .: "state"
    machineRegion <- o .: "region"
    imageRef <- o .: "image_ref"
    machineImage <- imageRef .: "digest"
    machineCreatedAt <- o .: "created_at"
    pure $ MachineResponse machineId machineState machineRegion machineImage machineCreatedAt

-- | Create Fly.io config from environment variables
getFlyIOConfig :: IO (Either String FlyIOConfig)
getFlyIOConfig = do
  mToken <- lookupEnv "FLY_API_TOKEN"
  mAppName <- lookupEnv "FLY_APP_NAME"
  let apiBase = "https://api.machines.dev/v1"
  
  case (mToken, mAppName) of
    (Just token, Just appName) ->
      pure $ Right $ FlyIOConfig (T.pack token) (T.pack appName) (T.pack apiBase)
    (Nothing, _) -> pure $ Left "FLY_API_TOKEN not set"
    (_, Nothing) -> pure $ Left "FLY_APP_NAME not set"

-- | Create a new machine in specified region
createMachine :: FlyIOConfig -> MachineConfig -> IO (Either String MachineResponse)
createMachine config machineConfig = do
  let appName = flyIOAppName config
  let apiBase = flyIOApiBase config
  let token = flyIOApiToken config
  
  let url = T.unpack $ apiBase <> "/apps/" <> appName <> "/machines"
  
  request <- parseRequest_ url
  let body = Aeson.encode machineConfig
  let request' = setRequestMethod "POST"
        $ setRequestHeader "Authorization" [TE.encodeUtf8 $ "Bearer " <> token]
        $ setRequestHeader "Content-Type" ["application/json"]
        $ setRequestBodyLBS body
        $ request
  
  result <- try $ httpLBS request'
  case result of
    Left (err :: IOException) -> pure $ Left $ "HTTP error: " ++ show err
    Right response -> do
      let status = getResponseStatus response
      if Status.statusCode status == 201
        then do
          let bodyBytes = getResponseBody response
          case Aeson.eitherDecode bodyBytes of
            Left err -> pure $ Left $ "Failed to decode machine response: " ++ err
            Right machineResp -> pure $ Right machineResp
        else pure $ Left $ "Failed to create machine: HTTP " ++ show (Status.statusCode status)

-- | Get machine by ID
getMachine :: FlyIOConfig -> Text -> IO (Either String MachineResponse)
getMachine config machineId = do
  let appName = flyIOAppName config
  let apiBase = flyIOApiBase config
  let token = flyIOApiToken config
  
  let url = T.unpack $ apiBase <> "/apps/" <> appName <> "/machines/" <> T.unpack machineId
  
  request <- parseRequest_ url
  let request' = setRequestMethod "GET"
        $ setRequestHeader "Authorization" [TE.encodeUtf8 $ "Bearer " <> token]
        $ request
  
  result <- try $ httpJSON request'
  case result of
    Left (err :: IOException) -> pure $ Left $ "HTTP error: " ++ show err
    Right response -> do
      let status = getResponseStatus response
      if Status.statusCode status == 200
        then do
          let machineResp = getResponseBody response :: MachineResponse
          pure $ Right machineResp
        else pure $ Left $ "Failed to get machine: HTTP " ++ show (Status.statusCode status)

-- | Start a machine
startMachine :: FlyIOConfig -> Text -> IO (Either String ())
startMachine config machineId = do
  let appName = flyIOAppName config
  let apiBase = flyIOApiBase config
  let token = flyIOApiToken config
  
  let url = T.unpack $ apiBase <> "/apps/" <> appName <> "/machines/" <> T.unpack machineId <> "/start"
  
  request <- parseRequest_ url
  let request' = setRequestMethod "POST"
        $ setRequestHeader "Authorization" [TE.encodeUtf8 $ "Bearer " <> token]
        $ request
  
  result <- try $ httpJSON request'
  case result of
    Left (err :: IOException) -> pure $ Left $ "HTTP error: " ++ show err
    Right response -> do
      let status = getResponseStatus response
      if Status.statusCode status == 200
        then pure $ Right ()
        else pure $ Left $ "Failed to start machine: HTTP " ++ show (Status.statusCode status)

-- | Stop a machine
stopMachine :: FlyIOConfig -> Text -> IO (Either String ())
stopMachine config machineId = do
  let appName = flyIOAppName config
  let apiBase = flyIOApiBase config
  let token = flyIOApiToken config
  
  let url = T.unpack $ apiBase <> "/apps/" <> appName <> "/machines/" <> T.unpack machineId <> "/stop"
  
  request <- parseRequest_ url
  let request' = setRequestMethod "POST"
        $ setRequestHeader "Authorization" [TE.encodeUtf8 $ "Bearer " <> token]
        $ request
  
  result <- try $ httpJSON request'
  case result of
    Left (err :: IOException) -> pure $ Left $ "HTTP error: " ++ show err
    Right response -> do
      let status = getResponseStatus response
      if Status.statusCode status == 200
        then pure $ Right ()
        else pure $ Left $ "Failed to stop machine: HTTP " ++ show (Status.statusCode status)

-- | Delete a machine
deleteMachine :: FlyIOConfig -> Text -> IO (Either String ())
deleteMachine config machineId = do
  let appName = flyIOAppName config
  let apiBase = flyIOApiBase config
  let token = flyIOApiToken config
  
  let url = T.unpack $ apiBase <> "/apps/" <> appName <> "/machines/" <> T.unpack machineId
  
  request <- parseRequest_ url
  let request' = setRequestMethod "DELETE"
        $ setRequestHeader "Authorization" [TE.encodeUtf8 $ "Bearer " <> token]
        $ request
  
  result <- try $ httpJSON request'
  case result of
    Left (err :: IOException) -> pure $ Left $ "HTTP error: " ++ show err
    Right response -> do
      let status = getResponseStatus response
      if Status.statusCode status == 200 || Status.statusCode status == 404
        then pure $ Right ()
        else pure $ Left $ "Failed to delete machine: HTTP " ++ show (Status.statusCode status)
