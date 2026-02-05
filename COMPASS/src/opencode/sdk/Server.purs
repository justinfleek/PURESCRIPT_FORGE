-- | SDK Server - Spawn and manage OpenCode server processes
-- | Phase 4: SDK Migration
module Opencode.SDK.Server where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Node.ChildProcess as CP

-- | Server options
type ServerOptions =
  { hostname :: Maybe String
  , port :: Maybe Int
  , signal :: Maybe AbortSignal
  , timeout :: Maybe Int
  , config :: Maybe Config
  }

-- | Config type (from generated types)
type Config =
  { logLevel :: Maybe String
  }

-- | AbortSignal type (FFI)
foreign import data AbortSignal :: Type

-- | Server instance
type Server =
  { url :: String
  , close :: Aff Unit
  }

-- | TUI options
type TuiOptions =
  { project :: Maybe String
  , model :: Maybe String
  , session :: Maybe String
  , agent :: Maybe String
  , signal :: Maybe AbortSignal
  , config :: Maybe Config
  }

-- | Create an OpenCode server
createOpencodeServer :: ServerOptions -> Aff (Either String Server)
createOpencodeServer options = do
  -- Default options
  let hostname = fromMaybe "127.0.0.1" options.hostname
  let port = fromMaybe 4096 options.port
  let timeout = fromMaybe 5000 options.timeout
  
  -- Build command arguments
  let args = ["serve", "--hostname=" <> hostname, "--port=" <> show port]
  let argsWithLogLevel = case options.config >>= _.logLevel of
        Just logLevel -> Array.snoc args ("--log-level=" <> logLevel)
        Nothing -> args
  
  -- Spawn process
  result <- spawnOpencodeProcess argsWithLogLevel options.signal options.config # liftEffect
  
  case result of
    Left err -> pure $ Left err
    Right proc -> do
      -- Wait for server to start and extract URL
      urlResult <- waitForServerUrl proc timeout
      case urlResult of
        Left err -> do
          _ <- CP.kill proc
          pure $ Left err
        Right url -> do
          pure $ Right
            { url: url
            , close: CP.kill proc
            }

-- | Create OpenCode TUI
createOpencodeTui :: TuiOptions -> Aff (Either String TuiInstance)
createOpencodeTui options = do
  -- Build command arguments
  let args = Array.catMaybes
        [ map (\p -> "--project=" <> p) options.project
        , map (\m -> "--model=" <> m) options.model
        , map (\s -> "--session=" <> s) options.session
        , map (\a -> "--agent=" <> a) options.agent
        ]
  
  -- Spawn process
  result <- spawnOpencodeTuiProcess args options.signal options.config # liftEffect
  
  case result of
    Left err -> pure $ Left err
    Right proc -> do
      pure $ Right
        { close: CP.kill proc
        }

-- | TUI instance
type TuiInstance =
  { close :: Aff Unit
  }

-- | Wait for server URL from process output
waitForServerUrl :: CP.ChildProcess -> Int -> Aff (Either String String)
waitForServerUrl proc timeout = do
  -- Use FFI to read process output and parse URL
  result <- waitForServerUrlFFI proc timeout
  pure result

-- | Wait for server URL from process output (FFI)
foreign import waitForServerUrlFFI :: CP.ChildProcess -> Int -> Aff (Either String String)

-- | Spawn opencode process
foreign import spawnOpencodeProcess :: Array String -> Maybe AbortSignal -> Maybe Config -> Effect (Either String CP.ChildProcess)

-- | Spawn opencode TUI process
foreign import spawnOpencodeTuiProcess :: Array String -> Maybe AbortSignal -> Maybe Config -> Effect (Either String CP.ChildProcess)
