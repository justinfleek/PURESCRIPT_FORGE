-- | CLI Network utilities
module Opencode.CLI.Network where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Bridge.FFI.Node.Fetch as Fetch

-- | Network configuration
type NetworkConfig =
  { host :: String
  , port :: Int
  , timeout :: Int
  }

-- | Check if a server is available
checkServer :: String -> Aff (Either String Boolean)
checkServer url = do
  result <- Fetch.fetch url { method: "GET", headers: {} } # liftEffect
  case result of
    Left err -> pure $ Left ("Failed to connect: " <> err)
    Right _ -> pure $ Right true

-- | Get available port
findAvailablePort :: Int -> Aff (Either String Int)
findAvailablePort startPort = do
  port <- findAvailablePortFFI startPort # liftEffect
  pure $ Right port

foreign import findAvailablePortFFI :: Int -> Effect Int
