-- | Bridge Server Main Entry Point
-- | PureScript implementation
module Bridge.Main where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Bridge.FFI.Node.Express as Express
import Bridge.FFI.Node.WebSocket as WS
import Bridge.FFI.Node.Pino as Pino
import Bridge.State.Store as Store
import Bridge.Config (loadConfig)
import Bridge.Server (startServer)

-- | Main entry point
main :: Effect Unit
main = launchAff_ do
  config <- liftEffect loadConfig
  
  logger <- liftEffect $ Pino.create
    { name: "bridge-server"
    , level: "info"
    }
  
  liftEffect $ Pino.info logger "Starting Bridge Server"
  
  store <- liftEffect Store.createStore
  
  startServer config store logger
