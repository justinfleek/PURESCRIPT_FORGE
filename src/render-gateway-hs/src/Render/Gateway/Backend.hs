{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}

-- | Render Gateway Backend Selection
-- | Backend selection with circuit breaker and load balancing
module Render.Gateway.Backend where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Data.Int (Int32)
import Data.Time (UTCTime)
import Data.List (minimumBy)
import Data.Ord (comparing)
import Render.Gateway.STM.CircuitBreaker (CircuitBreaker, isAvailable, recordSuccess, recordFailure)
import Render.Gateway.STM.Clock (Clock, readClockSTM)

-- | Backend configuration
data Backend = Backend
  { beId :: String
  , beFamily :: String -- model family (flux, wan, qwen)
  , beModels :: [String] -- supported models
  , beEndpoint :: String -- gRPC endpoint
  , beCapacity :: Int32 -- max concurrent requests
  , beInFlight :: TVar Int32 -- current in-flight requests
  , beCircuit :: CircuitBreaker
  }

-- | Select backend for request
selectBackend :: [Backend] -> String -> String -> Clock -> STM (Maybe Backend)
selectBackend backends family model clock = do
  (_, now) <- readClockSTM clock
  
  -- Filter by family/model
  let candidates = filter (\b -> beFamily b == family && model `elem` beModels b) backends
  
  -- Check availability (circuit breaker + capacity)
  availableBackends <- filterM (\b -> do
    available <- isAvailable (beCircuit b) now
    inFlight <- readTVar (beInFlight b)
    pure (available && inFlight < beCapacity b)
  ) candidates
  
  case availableBackends of
    [] -> pure Nothing
    xs -> do
      -- Select backend with lowest load
      loads <- mapM (\b -> readTVar (beInFlight b)) xs
      let selected = fst $ minimumBy (comparing snd) (zip xs loads)
      
      -- Increment in-flight count
      modifyTVar' (beInFlight selected) (+ 1)
      
      pure (Just selected)

-- | Release backend (decrement in-flight)
releaseBackend :: Backend -> STM ()
releaseBackend Backend {..} = do
  modifyTVar' beInFlight (\n -> max 0 (n - 1))

-- | Record backend success
recordBackendSuccess :: Backend -> STM ()
recordBackendSuccess Backend {..} = do
  recordSuccess beCircuit
  releaseBackend Backend {..}

-- | Record backend failure
recordBackendFailure :: Backend -> UTCTime -> STM ()
recordBackendFailure Backend {..} now = do
  recordFailure beCircuit now
  releaseBackend Backend {..}
