-- | Forge Client
-- | PureScript implementation
module Bridge.Forge.Client where

import Prelude
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..))
import Bridge.State.Store (StateStore)
import Bridge.FFI.Node.Pino as Pino
import Bridge.FFI.Forge.SDK as SDK

-- | Opaque Forge Client type
foreign import data ForgeClient :: Type

-- | Create Forge client
createForgeClient :: StateStore -> { apiUrl :: String, directory :: String } -> Pino.Logger -> Aff (Maybe ForgeClient)
createForgeClient store config logger = do
  liftEffect $ Pino.info logger "Creating Forge client"
  
  -- Create SDK client
  clientResult <- SDK.createClient
    { baseUrl: config.apiUrl
    , directory: config.directory
    }
  
  case clientResult of
    Left err -> do
      liftEffect $ Pino.warn logger ("Failed to create Forge client: " <> err)
      pure Nothing
    Right sdkClient -> do
      -- Connect client
      connectResult <- SDK.connect sdkClient
      case connectResult of
        Left err -> do
          liftEffect $ Pino.warn logger ("Failed to connect Forge client: " <> err)
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
              liftEffect $ Pino.info logger "Forge client connected and subscribed to events"
              launchAff_ $ processEventStream store logger stream
              pure (Just (wrapClient sdkClient))
  where
    foreign import wrapClient :: SDK.SDKClient -> ForgeClient
    foreign import processEventStream :: StateStore -> Pino.Logger -> SDK.EventStream -> Aff Unit
