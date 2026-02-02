-- | OpenCode Client
-- | PureScript implementation
module Bridge.Opencode.Client where

import Prelude
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..))
import Bridge.State.Store (StateStore)
import Bridge.FFI.Node.Pino as Pino
import Bridge.FFI.OpenCode.SDK as SDK

-- | Opaque OpenCode Client type
foreign import data OpencodeClient :: Type

-- | Create OpenCode client
createOpencodeClient :: StateStore -> { apiUrl :: String, directory :: String } -> Pino.Logger -> Aff (Maybe OpencodeClient)
createOpencodeClient store config logger = do
  liftEffect $ Pino.info logger "Creating OpenCode client"
  
  -- Create SDK client
  clientResult <- SDK.createClient
    { baseUrl: config.apiUrl
    , directory: config.directory
    }
  
  case clientResult of
    Left err -> do
      liftEffect $ Pino.warn logger ("Failed to create OpenCode client: " <> err)
      pure Nothing
    Right sdkClient -> do
      -- Connect client
      connectResult <- SDK.connect sdkClient
      case connectResult of
        Left err -> do
          liftEffect $ Pino.warn logger ("Failed to connect OpenCode client: " <> err)
          pure Nothing
        Right _ -> do
          -- Subscribe to events
          streamResult <- SDK.subscribeEvents sdkClient
          case streamResult of
            Left err -> do
              liftEffect $ Pino.warn logger ("Failed to subscribe to events: " <> err)
              pure (Just (wrapClient sdkClient))
            Right stream -> do
              -- Start processing events
              liftEffect $ Pino.info logger "OpenCode client connected and subscribed to events"
              launchAff_ $ processEventStream store logger stream
              pure (Just (wrapClient sdkClient))
  where
    foreign import wrapClient :: SDK.SDKClient -> OpencodeClient
    foreign import processEventStream :: StateStore -> Pino.Logger -> SDK.EventStream -> Aff Unit
