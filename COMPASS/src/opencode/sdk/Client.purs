-- | SDK Client - Create and configure OpenCode API clients
-- | Phase 4: SDK Migration
module Opencode.SDK.Client where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (encodeJson, decodeJson, jsonParser, (.:), (.:?))
import Bridge.FFI.Node.Fetch as Fetch
import Opencode.SDK.Server as Server
import Opencode.SDK.Gen.Types as Types

-- | Client configuration
type ClientConfig =
  { baseUrl :: Maybe String
  , directory :: Maybe String
  , headers :: Maybe (Array { key :: String, value :: String })
  , fetch :: Maybe (String -> Fetch.FetchOptions -> Aff (Either String Fetch.Response))
  }

-- | OpencodeClient wrapper with API methods
type OpencodeClient =
  { client :: Client
  , global :: GlobalClient
  , session :: SessionClient
  , project :: ProjectClient
  , config :: ConfigClient
  }

-- | Internal client type
type Client =
  { baseUrl :: String
  , config :: ClientConfig
  }

-- | Global API client
type GlobalClient =
  { health :: Aff (Either String Types.Health)
  }

-- | Session API client
type SessionClient =
  { list :: Aff (Either String (Array Types.Session))
  , get :: String -> Aff (Either String Types.Session)
  , create :: Types.Session -> Aff (Either String Types.Session)
  }

-- | Project API client
type ProjectClient =
  { list :: Aff (Either String (Array Types.Session))
  , current :: Aff (Either String Types.Session)
  }

-- | Config API client
type ConfigClient =
  { get :: Aff (Either String Types.Config)
  , update :: Types.Config -> Aff (Either String Types.Config)
  }

-- | Create an OpenCode client
createOpencodeClient :: ClientConfig -> OpencodeClient
createOpencodeClient config = do
  -- Merge config with defaults
  let mergedConfig = mergeConfig config defaultConfig
  let baseUrl = fromMaybe "http://localhost:4096" mergedConfig.baseUrl
  
  -- Add directory header if provided
  let headersWithDirectory = case mergedConfig.directory of
        Just dir -> do
          let encodedDir = encodeURIComponent dir
          let dirHeader = { key: "x-opencode-directory", value: encodedDir }
          case mergedConfig.headers of
            Just existing -> Just (Array.snoc existing dirHeader)
            Nothing -> Just [dirHeader]
        Nothing -> mergedConfig.headers
  
  -- Create internal client
  let client = { baseUrl, config: mergedConfig }
  
  -- Create API clients
  let globalClient = createGlobalClient client
  let sessionClient = createSessionClient client
  let projectClient = createProjectClient client
  let configClient = createConfigClient client
  
  { client
  , global: globalClient
  , session: sessionClient
  , project: projectClient
  , config: configClient
  }
  where
    mergeConfig :: ClientConfig -> ClientConfig -> ClientConfig
    mergeConfig user default_ =
      { baseUrl: fromMaybe default_.baseUrl user.baseUrl
      , directory: user.directory
      , headers: user.headers
      , fetch: fromMaybe default_.fetch user.fetch
      }
    
    encodeURIComponent :: String -> String
    encodeURIComponent = encodeURIComponentFFI
    
foreign import encodeURIComponentFFI :: String -> String
    
    createGlobalClient :: Client -> GlobalClient
    createGlobalClient c =
      { health: fetchGet (c.baseUrl <> "/global/health") c.config
      }
    
    createSessionClient :: Client -> SessionClient
    createSessionClient c =
      { list: fetchGet (c.baseUrl <> "/session") c.config
      , get: \id -> fetchGet (c.baseUrl <> "/session/" <> id) c.config
      , create: \body -> fetchPost (c.baseUrl <> "/session") body c.config
      }
    
    createProjectClient :: Client -> ProjectClient
    createProjectClient c =
      { list: fetchGet (c.baseUrl <> "/project") c.config
      , current: fetchGet (c.baseUrl <> "/project/current") c.config
      }
    
    createConfigClient :: Client -> ConfigClient
    createConfigClient c =
      { get: fetchGet (c.baseUrl <> "/config") c.config
      , update: \body -> fetchPatch (c.baseUrl <> "/config") body c.config
      }
    
    fetchGet :: forall a. String -> ClientConfig -> Aff (Either String a)
    fetchGet url cfg = do
      result <- Fetch.fetch url { method: "GET", headers: fromMaybe [] cfg.headers } # liftEffect
      case result of
        Left err -> pure $ Left err
        Right resp -> do
          isOk <- liftEffect $ Fetch.ok resp
          statusCode <- liftEffect $ Fetch.status resp
          if not isOk
            then do
              textResult <- Fetch.text resp
              case textResult of
                Left _ -> pure $ Left ("HTTP " <> show statusCode)
                Right body -> pure $ Left ("HTTP " <> show statusCode <> ": " <> body)
            else do
              textResult <- Fetch.text resp
              case textResult of
                Left err -> pure $ Left ("Failed to read response: " <> err)
                Right body -> case jsonParser body of
                  Left err -> pure $ Left ("JSON parse error: " <> show err)
                  Right json -> case decodeJson json of
                    Left err -> pure $ Left ("JSON decode error: " <> show err)
                    Right value -> pure $ Right value
    
    fetchPost :: forall a b. String -> a -> ClientConfig -> Aff (Either String b)
    fetchPost url body cfg = do
      let headers = Array.snoc (fromMaybe [] cfg.headers) { key: "Content-Type", value: "application/json" }
      result <- Fetch.fetch url { method: "POST", headers: headers, body: Just (encodeJson body) } # liftEffect
      case result of
        Left err -> pure $ Left err
        Right resp -> do
          isOk <- liftEffect $ Fetch.ok resp
          statusCode <- liftEffect $ Fetch.status resp
          if not isOk
            then do
              textResult <- Fetch.text resp
              case textResult of
                Left _ -> pure $ Left ("HTTP " <> show statusCode)
                Right body -> pure $ Left ("HTTP " <> show statusCode <> ": " <> body)
            else do
              textResult <- Fetch.text resp
              case textResult of
                Left err -> pure $ Left ("Failed to read response: " <> err)
                Right body -> case jsonParser body of
                  Left err -> pure $ Left ("JSON parse error: " <> show err)
                  Right json -> case decodeJson json of
                    Left err -> pure $ Left ("JSON decode error: " <> show err)
                    Right value -> pure $ Right value
    
    fetchPatch :: forall a b. String -> a -> ClientConfig -> Aff (Either String b)
    fetchPatch url body cfg = do
      let headers = Array.snoc (fromMaybe [] cfg.headers) { key: "Content-Type", value: "application/json" }
      result <- Fetch.fetch url { method: "PATCH", headers: headers, body: Just (encodeJson body) } # liftEffect
      case result of
        Left err -> pure $ Left err
        Right resp -> do
          isOk <- liftEffect $ Fetch.ok resp
          statusCode <- liftEffect $ Fetch.status resp
          if not isOk
            then do
              textResult <- Fetch.text resp
              case textResult of
                Left _ -> pure $ Left ("HTTP " <> show statusCode)
                Right body -> pure $ Left ("HTTP " <> show statusCode <> ": " <> body)
            else do
              textResult <- Fetch.text resp
              case textResult of
                Left err -> pure $ Left ("Failed to read response: " <> err)
                Right body -> case jsonParser body of
                  Left err -> pure $ Left ("JSON parse error: " <> show err)
                  Right json -> case decodeJson json of
                    Left err -> pure $ Left ("JSON decode error: " <> show err)
                    Right value -> pure $ Right value

-- | Default client configuration
defaultConfig :: ClientConfig
defaultConfig =
  { baseUrl: Nothing
  , directory: Nothing
  , headers: Nothing
  , fetch: Nothing
  }

-- | OpencodeSDK type (returned from createOpencode)
type OpencodeSDK =
  { client :: OpencodeClient
  , server :: Server.Server
  }
