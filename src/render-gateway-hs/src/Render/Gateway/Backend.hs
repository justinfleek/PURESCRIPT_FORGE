{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Render Gateway Backend Selection
-- | Backend selection with circuit breaker and load balancing
module Render.Gateway.Backend where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Control.Monad (filterM)
import Data.Int (Int32)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Time (UTCTime)
import Data.List (minimumBy)
import Data.Ord (comparing)
import Render.Gateway.STM.CircuitBreaker (CircuitBreaker, isAvailable, recordSuccess, recordFailure)
import Render.Gateway.STM.Clock (Clock, readClockSTM)

-- | Backend type (inference engine)
data BackendType = Nunchaku | Torch | TensorRT
  deriving (Eq, Ord, Show)

-- | Backend configuration
data Backend = Backend
  { beId :: Text            -- Backend ID
  , beType :: BackendType   -- nunchaku, torch, tensorrt
  , beFamily :: Text        -- model family (flux, wan, qwen)
  , beModels :: [Text]      -- supported models
  , beEndpoint :: Text      -- HTTP/gRPC endpoint
  , beCapacity :: Int32     -- max concurrent requests
  , beInFlight :: TVar Int32 -- current in-flight requests
  , beCircuit :: CircuitBreaker
  }

-- | Select backend for request
-- | Matches by family, model, and optionally backend type
selectBackend :: [Backend] -> Text -> Text -> Maybe Text -> Clock -> STM (Maybe Backend)
selectBackend backends family model mBackendType clock = do
  (_, now) <- readClockSTM clock

  -- Filter by family/model
  let familyMatches = filter (\b -> beFamily b == family && model `elem` beModels b) backends

  -- Optionally filter by backend type
  let candidates = case mBackendType of
        Nothing -> familyMatches
        Just bt -> filter (\b -> Text.toLower (Text.pack (show (beType b))) == Text.toLower bt) familyMatches

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

-- | Select backend by explicit type preference
selectBackendByType :: [Backend] -> Text -> Text -> BackendType -> Clock -> STM (Maybe Backend)
selectBackendByType backends family model backendType clock =
  selectBackend backends family model (Just (Text.pack (show backendType))) clock

-- | Release backend (decrement in-flight)
releaseBackend :: Backend -> STM ()
releaseBackend Backend {..} = do
  modifyTVar' beInFlight (\n -> max 0 (n - 1))

-- | Record backend success
recordBackendSuccess :: Backend -> STM ()
recordBackendSuccess backend@Backend {..} = do
  recordSuccess beCircuit
  releaseBackend backend

-- | Record backend failure
recordBackendFailure :: Backend -> UTCTime -> STM ()
recordBackendFailure backend@Backend {..} now = do
  recordFailure beCircuit now
  releaseBackend backend

-- | Parse backend type from text
parseBackendType :: Text -> Maybe BackendType
parseBackendType t = case Text.toLower t of
  "nunchaku" -> Just Nunchaku
  "torch" -> Just Torch
  "tensorrt" -> Just TensorRT
  _ -> Nothing
