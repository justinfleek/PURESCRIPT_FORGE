{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Render Gateway Main Entry Point
-- | Starts HTTP server with STM gateway
module Main where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Render.Gateway.STM.Queue (createQueue)
import Render.Gateway.STM.Clock (createClock, startClockThread)
import Render.Gateway.STM.CircuitBreaker (createCircuitBreaker, CircuitBreakerConfig(..))
import Render.Gateway.STM.RateLimiter (RateLimiter)
import Render.Gateway.Backend (Backend(..), BackendType(..))
import Render.Gateway.Core (GatewayState(..), JobStore(..), createJobStore)
import Render.Gateway.Server (startServer)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Int (Int32)
import Data.Text (Text)
import Data.Time (getCurrentTime)
import System.Environment (lookupEnv)
import Text.Read (readMaybe)

main :: IO ()
main = do
  -- Get port from environment or default to 8080
  portEnv <- lookupEnv "PORT"
  let port = maybe 8080 id (portEnv >>= readMaybe)

  -- Get backend endpoint from environment or default to localhost
  backendHost <- maybe "localhost:8001" id <$> lookupEnv "BACKEND_HOST"

  putStrLn "==================================="
  putStrLn "  Render Gateway - Weyl AI"
  putStrLn "==================================="
  putStrLn ""

  -- Initialize clock
  clock <- createClock
  _clockThread <- startClockThread clock
  putStrLn "[OK] Clock initialized"

  -- Initialize queue
  queue <- atomically createQueue
  putStrLn "[OK] Request queue initialized"

  -- Initialize job store
  jobStore <- atomically createJobStore
  putStrLn "[OK] Job store initialized"

  -- Initialize rate limiters map
  rateLimiters <- atomically (newTVar (Map.empty :: Map Text RateLimiter))
  putStrLn "[OK] Rate limiters initialized"

  -- Create circuit breaker config
  let circuitConfig = CircuitBreakerConfig
        { cbcFailureThreshold = 0.5
        , cbcSuccessThreshold = 5
        , cbcTimeoutSeconds = 60
        , cbcWindowSize = 100
        }

  -- Create backends for each model family
  initialTime <- getCurrentTime

  -- Flux backend (image generation)
  fluxCircuit <- atomically (createCircuitBreaker initialTime circuitConfig)
  fluxInFlight <- atomically (newTVar (0 :: Int32))
  let fluxBackend = Backend
        { beId = "flux-triton-1"
        , beType = Nunchaku
        , beFamily = "flux"
        , beModels = ["flux-dev", "flux-dev2", "flux-schnell"]
        , beEndpoint = backendHost
        , beCapacity = 100
        , beInFlight = fluxInFlight
        , beCircuit = fluxCircuit
        }

  -- WAN backend (video generation)
  wanCircuit <- atomically (createCircuitBreaker initialTime circuitConfig)
  wanInFlight <- atomically (newTVar (0 :: Int32))
  let wanBackend = Backend
        { beId = "wan-triton-1"
        , beType = Torch
        , beFamily = "wan"
        , beModels = ["wan-2.1", "wan-2.1-turbo", "wan-1.3b"]
        , beEndpoint = backendHost
        , beCapacity = 50
        , beInFlight = wanInFlight
        , beCircuit = wanCircuit
        }

  -- Qwen backend (video generation)
  qwenCircuit <- atomically (createCircuitBreaker initialTime circuitConfig)
  qwenInFlight <- atomically (newTVar (0 :: Int32))
  let qwenBackend = Backend
        { beId = "qwen-triton-1"
        , beType = TensorRT
        , beFamily = "qwen"
        , beModels = ["qwen-2.5-vl"]
        , beEndpoint = backendHost
        , beCapacity = 25
        , beInFlight = qwenInFlight
        , beCircuit = qwenCircuit
        }

  -- SDXL backend (image generation)
  sdxlCircuit <- atomically (createCircuitBreaker initialTime circuitConfig)
  sdxlInFlight <- atomically (newTVar (0 :: Int32))
  let sdxlBackend = Backend
        { beId = "sdxl-triton-1"
        , beType = Torch
        , beFamily = "sdxl"
        , beModels = ["sdxl-1.0", "sdxl-turbo"]
        , beEndpoint = backendHost
        , beCapacity = 100
        , beInFlight = sdxlInFlight
        , beCircuit = sdxlCircuit
        }

  -- ZImage backend (image generation)
  zimageCircuit <- atomically (createCircuitBreaker initialTime circuitConfig)
  zimageInFlight <- atomically (newTVar (0 :: Int32))
  let zimageBackend = Backend
        { beId = "zimage-triton-1"
        , beType = Nunchaku
        , beFamily = "zimage"
        , beModels = ["zimage-1.0"]
        , beEndpoint = backendHost
        , beCapacity = 100
        , beInFlight = zimageInFlight
        , beCircuit = zimageCircuit
        }

  let allBackends = [fluxBackend, wanBackend, qwenBackend, sdxlBackend, zimageBackend]
  putStrLn $ "[OK] " <> show (length allBackends) <> " backends configured"

  -- Create gateway state
  let gatewayState = GatewayState
        { gsQueue = queue
        , gsJobStore = jobStore
        , gsRateLimiters = rateLimiters
        , gsBackends = allBackends
        , gsClock = clock
        }

  putStrLn ""
  putStrLn "Configured models:"
  putStrLn "  [video] wan: wan-2.1, wan-2.1-turbo, wan-1.3b"
  putStrLn "  [video] qwen: qwen-2.5-vl"
  putStrLn "  [image] flux: flux-dev, flux-dev2, flux-schnell"
  putStrLn "  [image] sdxl: sdxl-1.0, sdxl-turbo"
  putStrLn "  [image] zimage: zimage-1.0"
  putStrLn ""

  -- Start HTTP server
  startServer port gatewayState
