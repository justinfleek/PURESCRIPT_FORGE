-- | Bridge Server Main Entry Point
-- | PureScript implementation for Nexus Bridge Server
module Bridge.Main where

import Prelude
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Bridge.FFI.Node.Pino as Pino
import Bridge.State.Store as Store
import Bridge.Config (loadConfig)
import Bridge.Server (startServer)

-- | Main entry point
main :: Effect Unit
main = launchAff_ do
  config <- liftEffect loadConfig
  
  logger <- liftEffect $ Pino.create
    { name: "nexus-bridge-server"
    , level: "info"
    }
  
  liftEffect $ Pino.info logger "Starting Nexus Bridge Server"
  
  store <- liftEffect Store.createStore
  
  startServer config store logger
