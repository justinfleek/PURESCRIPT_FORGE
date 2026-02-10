-- | Bridge Main - Entry point for the bridge server
module Bridge.Main where

import Prelude
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Bridge.FFI.Node.Pino as Pino
import Bridge.State.Store (createStore)
import Bridge.Config (loadConfig)
import Bridge.Server (startServer)

-- | Main entry point
main :: Effect Unit
main = launchAff_ do
  config <- liftEffect loadConfig
  logger <- liftEffect $ Pino.create { name: "bridge-server", level: "info" }
  liftEffect $ Pino.info logger "Starting bridge server..."
  store <- liftEffect createStore
  startServer config store logger
