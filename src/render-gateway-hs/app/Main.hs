{-# LANGUAGE StrictData #-}

-- | Render Gateway Main Entry Point
-- | Starts HTTP server with STM gateway
module Main where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Control.Monad.IO.Class (liftIO)
import Render.Gateway.STM.Queue (createQueue)
import Render.Gateway.STM.Clock (createClock, startClockThread)
import Render.Gateway.STM.CircuitBreaker (createCircuitBreaker, CircuitBreakerConfig(..))
import Render.Gateway.STM.RateLimiter (RateLimiter)
import Render.Gateway.Backend (Backend(..))
import Render.Gateway.Core (GatewayState(..))
import Render.Gateway.Server (startServer)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Int (Int32)
import Data.Time (getCurrentTime)
import Control.Concurrent.STM (atomically, newTVar)

main :: IO ()
main = do
  -- Initialize clock
  clock <- createClock
  _clockThread <- startClockThread clock
  
  -- Initialize queue
  queue <- atomically createQueue
  
  -- Initialize rate limiters map
  rateLimiters <- atomically (newTVar (Map.empty :: Map String RateLimiter))
  
  -- Create circuit breaker config
  let circuitConfig = CircuitBreakerConfig
        { cbcFailureThreshold = 0.5
        , cbcSuccessThreshold = 5
        , cbcTimeoutSeconds = 60
        , cbcWindowSize = 100
        }
  
  -- Create sample backend
  now <- getCurrentTime
  initialTime <- getCurrentTime
  circuit <- atomically (createCircuitBreaker initialTime circuitConfig)
  inFlight <- atomically (newTVar (0 :: Int32))
  
  let backend = Backend
        { beId = "triton-1"
        , beFamily = "flux"
        , beModels = ["flux-dev", "flux-dev2", "flux-schnell"]
        , beEndpoint = "localhost:8001"
        , beCapacity = 100
        , beInFlight = inFlight
        , beCircuit = circuit
        }
  
  -- Create gateway state
  let gatewayState = GatewayState
        { gsQueue = queue
        , gsRateLimiters = rateLimiters
        , gsBackends = [backend]
        , gsClock = clock
        }
  
  -- Start HTTP server
  putStrLn "Starting Render Gateway on port 8080..."
  startServer 8080 gatewayState
