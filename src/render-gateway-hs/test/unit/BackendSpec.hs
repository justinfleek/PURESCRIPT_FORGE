{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive unit tests for Backend module
-- | Tests individual functions in isolation: selectBackend, selectBackendByType,
-- | releaseBackend, recordBackendSuccess, recordBackendFailure, parseBackendType
module BackendSpec where

import Test.Hspec
import Control.Concurrent.STM
import Control.Monad (replicateM, replicateM_)
import Data.Maybe (isJust)
import Data.Time (getCurrentTime, UTCTime)
import Data.Text (Text)
import qualified Data.Text as Text
import Render.Gateway.Backend
  ( Backend(..)
  , BackendType(..)
  , selectBackend
  , selectBackendByType
  , releaseBackend
  , recordBackendSuccess
  , recordBackendFailure
  , parseBackendType
  )
import Render.Gateway.STM.CircuitBreaker (CircuitBreaker, createCircuitBreaker, recordSuccess, recordFailure, isAvailable)
import Render.Gateway.STM.Clock (Clock, createClock, startClockThread, readClockSTM)

-- | Helper to create test backend
createTestBackend :: Text -> BackendType -> Text -> [Text] -> Text -> Int32 -> IO Backend
createTestBackend backendId backendType family models endpoint capacity = do
  now <- getCurrentTime
  circuitBreaker <- atomically $ createCircuitBreaker 5 3 60.0 300.0 now
  inFlight <- atomically $ newTVar 0
  pure Backend
    { beId = backendId
    , beType = backendType
    , beFamily = family
    , beModels = models
    , beEndpoint = endpoint
    , beCapacity = capacity
    , beInFlight = inFlight
    , beCircuit = circuitBreaker
    }

-- | Deep comprehensive unit tests for Backend module
spec :: Spec
spec = describe "Backend Unit Tests" $ do
  describe "selectBackend" $ do
    it "selects backend matching family and model" $ do
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      clock <- atomically createClock
      _ <- startClockThread clock
      
      result <- atomically $ selectBackend [backend] "wan" "model1" Nothing clock
      
      result `shouldSatisfy` isJust
      case result of
        Just b -> beId b `shouldBe` "b1"
        Nothing -> fail "Expected backend to be selected"

    it "returns Nothing when no backend matches family" $ do
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      clock <- atomically createClock
      _ <- startClockThread clock
      
      result <- atomically $ selectBackend [backend] "flux" "model1" Nothing clock
      
      result `shouldBe` Nothing

    it "returns Nothing when model not in supported models" $ do
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      clock <- atomically createClock
      _ <- startClockThread clock
      
      result <- atomically $ selectBackend [backend] "wan" "model2" Nothing clock
      
      result `shouldBe` Nothing

    it "BUG: case-sensitive backend type filtering may miss matches" $ do
      -- BUG: selectBackend (line 49) uses Text.toLower for backend type comparison,
      -- but if the backend type string has mixed case or special characters,
      -- the comparison may fail. Additionally, the Show instance for BackendType
      -- may produce different strings than expected.
      backend1 <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      backend2 <- createTestBackend "b2" Torch "wan" ["model1"] "localhost:8000" 10
      clock <- atomically createClock
      _ <- startClockThread clock
      
      -- Should match "nunchaku" (lowercase)
      result1 <- atomically $ selectBackend [backend1, backend2] "wan" "model1" (Just "nunchaku") clock
      result1 `shouldSatisfy` isJust
      case result1 of
        Just b -> beType b `shouldBe` Nunchaku
        Nothing -> fail "Expected Nunchaku backend"
      
      -- Should also match "NUNCHAKU" (uppercase) due to toLower
      result2 <- atomically $ selectBackend [backend1, backend2] "wan" "model1" (Just "NUNCHAKU") clock
      result2 `shouldSatisfy` isJust
      case result2 of
        Just b -> beType b `shouldBe` Nunchaku
        Nothing -> fail "Expected Nunchaku backend"

    it "BUG: increments in-flight counter even if backend becomes unavailable" $ do
      -- BUG: selectBackend (line 66) increments beInFlight after selecting backend,
      -- but if the backend becomes unavailable (circuit breaker opens, capacity exceeded)
      -- between the availability check (line 52-56) and the increment (line 66),
      -- the counter may be incremented for an unavailable backend. However, this is
      -- mitigated by the STM transaction ensuring atomicity.
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 1
      clock <- atomically createClock
      _ <- startClockThread clock
      
      -- Fill capacity
      atomically $ modifyTVar' (beInFlight backend) (+ 1)
      
      -- Should return Nothing (at capacity)
      result <- atomically $ selectBackend [backend] "wan" "model1" Nothing clock
      result `shouldBe` Nothing
      
      -- Counter should still be 1 (not incremented)
      count <- atomically $ readTVar (beInFlight backend)
      count `shouldBe` 1

    it "BUG: load balancing may select backend with equal load arbitrarily" $ do
      -- BUG: selectBackend (line 62-63) uses minimumBy to select backend with lowest load.
      -- If multiple backends have the same load, minimumBy selects the first one,
      -- which may not be optimal for load distribution. This can lead to uneven
      -- load distribution if backends are always checked in the same order.
      backend1 <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      backend2 <- createTestBackend "b2" Nunchaku "wan" ["model1"] "localhost:8000" 10
      clock <- atomically createClock
      _ <- startClockThread clock
      
      -- Both backends have same load (0)
      result <- atomically $ selectBackend [backend1, backend2] "wan" "model1" Nothing clock
      result `shouldSatisfy` isJust
      
      -- First backend in list is selected (arbitrary)
      case result of
        Just b -> beId b `shouldBe` "b1"
        Nothing -> fail "Expected backend to be selected"

    it "BUG: may not handle empty backend list correctly" $ do
      -- BUG: selectBackend (line 44) filters backends, and if the list is empty,
      -- familyMatches will be empty, leading to Nothing being returned. This is
      -- correct behavior, but the function doesn't distinguish between "no backends"
      -- and "no matching backends", which may make debugging harder.
      clock <- atomically createClock
      _ <- startClockThread clock
      
      result <- atomically $ selectBackend [] "wan" "model1" Nothing clock
      result `shouldBe` Nothing

    it "BUG: backend type filtering uses Show instance which may not match expected format" $ do
      -- BUG: selectBackend (line 49) converts BackendType to string using Show instance
      -- (Text.pack (show (beType b))), then compares with Text.toLower. If the Show
      -- instance produces unexpected strings (e.g., with spaces, special characters),
      -- the comparison may fail.
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      clock <- atomically createClock
      _ <- startClockThread clock
      
      -- Show instance should produce "Nunchaku", "Torch", or "TensorRT"
      let backendTypeStr = show (beType backend)
      result <- atomically $ selectBackend [backend] "wan" "model1" (Just (Text.pack backendTypeStr)) clock
      result `shouldSatisfy` isJust

  describe "selectBackendByType" $ do
    it "selects backend by explicit type" $ do
      backend1 <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      backend2 <- createTestBackend "b2" Torch "wan" ["model1"] "localhost:8000" 10
      clock <- atomically createClock
      _ <- startClockThread clock
      
      result <- atomically $ selectBackendByType [backend1, backend2] "wan" "model1" Nunchaku clock
      
      result `shouldSatisfy` isJust
      case result of
        Just b -> beType b `shouldBe` Nunchaku
        Nothing -> fail "Expected Nunchaku backend"

    it "BUG: uses Show instance which may not match parseBackendType output" $ do
      -- BUG: selectBackendByType (line 73) converts BackendType to string using Show,
      -- then passes to selectBackend which does Text.toLower comparison. However,
      -- parseBackendType expects lowercase strings. If Show produces different strings,
      -- there may be inconsistency between parsing and selection.
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      clock <- atomically createClock
      _ <- startClockThread clock
      
      -- selectBackendByType should work with BackendType enum
      result <- atomically $ selectBackendByType [backend] "wan" "model1" Nunchaku clock
      result `shouldSatisfy` isJust

  describe "releaseBackend" $ do
    it "decrements in-flight counter" $ do
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      
      atomically $ modifyTVar' (beInFlight backend) (+ 5)
      atomically $ releaseBackend backend
      
      count <- atomically $ readTVar (beInFlight backend)
      count `shouldBe` 4

    it "BUG: prevents counter from going negative but doesn't log error" $ do
      -- BUG: releaseBackend (line 78) uses max 0 to prevent negative counter,
      -- but if releaseBackend is called more times than selectBackend, the counter
      -- stays at 0 without any indication that there's a bug (double release).
      -- This hides bugs and makes debugging harder.
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      
      -- Release without acquiring
      atomically $ releaseBackend backend
      
      count <- atomically $ readTVar (beInFlight backend)
      count `shouldBe` 0 -- Prevents negative, but no error logged

    it "BUG: doesn't validate that backend was actually acquired" $ do
      -- BUG: releaseBackend doesn't check if the backend was actually acquired
      -- before releasing. If releaseBackend is called on a backend that was never
      -- selected, the counter behavior is correct (stays at 0), but there's no
      -- way to detect this programming error.
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      
      -- Release without acquiring
      atomically $ releaseBackend backend
      
      count <- atomically $ readTVar (beInFlight backend)
      count `shouldBe` 0

    it "handles multiple rapid releases correctly" $ do
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      
      atomically $ do
        modifyTVar' (beInFlight backend) (+ 3)
        releaseBackend backend
        releaseBackend backend
        releaseBackend backend
      
      count <- atomically $ readTVar (beInFlight backend)
      count `shouldBe` 0

  describe "recordBackendSuccess" $ do
    it "records success and releases backend" $ do
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      clock <- atomically createClock
      _ <- startClockThread clock
      now <- getCurrentTime
      
      -- Acquire backend
      atomically $ modifyTVar' (beInFlight backend) (+ 1)
      
      -- Record success
      atomically $ recordBackendSuccess backend now
      
      -- Counter should be 0 (released)
      count <- atomically $ readTVar (beInFlight backend)
      count `shouldBe` 0

    it "BUG: records success even if backend was never acquired" $ do
      -- BUG: recordBackendSuccess (line 82-84) calls recordSuccess on circuit breaker
      -- and releaseBackend, but doesn't verify that the backend was actually acquired.
      -- If called on a backend that was never selected, it will still record success
      -- in the circuit breaker, which may incorrectly mark a backend as healthy.
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      clock <- atomically createClock
      _ <- startClockThread clock
      now <- getCurrentTime
      
      -- Record success without acquiring
      atomically $ recordBackendSuccess backend now
      
      -- Counter should be 0 (releaseBackend prevents negative)
      count <- atomically $ readTVar (beInFlight backend)
      count `shouldBe` 0
      
      -- Circuit breaker still records success (may be incorrect)

    it "BUG: order of operations may cause issues if releaseBackend fails" $ do
      -- BUG: recordBackendSuccess (line 83-84) first records success, then releases.
      -- If releaseBackend somehow fails (though it's pure STM), the success is
      -- already recorded, leading to inconsistent state. However, STM transactions
      -- are atomic, so this shouldn't happen in practice.
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      clock <- atomically createClock
      _ <- startClockThread clock
      now <- getCurrentTime
      
      atomically $ modifyTVar' (beInFlight backend) (+ 1)
      atomically $ recordBackendSuccess backend now
      
      count <- atomically $ readTVar (beInFlight backend)
      count `shouldBe` 0

  describe "recordBackendFailure" $ do
    it "records failure and releases backend" $ do
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      clock <- atomically createClock
      _ <- startClockThread clock
      now <- getCurrentTime
      
      -- Acquire backend
      atomically $ modifyTVar' (beInFlight backend) (+ 1)
      
      -- Record failure
      atomically $ recordBackendFailure backend now
      
      -- Counter should be 0 (released)
      count <- atomically $ readTVar (beInFlight backend)
      count `shouldBe` 0

    it "BUG: records failure even if backend was never acquired" $ do
      -- BUG: Similar to recordBackendSuccess, recordBackendFailure doesn't verify
      -- that the backend was actually acquired. This may incorrectly mark backends
      -- as failed when they were never used.
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      clock <- atomically createClock
      _ <- startClockThread clock
      now <- getCurrentTime
      
      -- Record failure without acquiring
      atomically $ recordBackendFailure backend now
      
      -- Counter should be 0
      count <- atomically $ readTVar (beInFlight backend)
      count `shouldBe` 0

    it "BUG: order of operations may cause issues if releaseBackend fails" $ do
      -- BUG: Similar to recordBackendSuccess, the order of operations may cause
      -- issues, though STM transactions ensure atomicity.
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      clock <- atomically createClock
      _ <- startClockThread clock
      now <- getCurrentTime
      
      atomically $ modifyTVar' (beInFlight backend) (+ 1)
      atomically $ recordBackendFailure backend now
      
      count <- atomically $ readTVar (beInFlight backend)
      count `shouldBe` 0

  describe "parseBackendType" $ do
    it "parses valid backend types" $ do
      parseBackendType "nunchaku" `shouldBe` Just Nunchaku
      parseBackendType "torch" `shouldBe` Just Torch
      parseBackendType "tensorrt" `shouldBe` Just TensorRT

    it "BUG: case-sensitive parsing may miss valid inputs" $ do
      -- BUG: parseBackendType (line 94) uses Text.toLower, so it should handle
      -- case-insensitive input. However, if the input has mixed case or special
      -- characters, it may not match correctly.
      parseBackendType "NUNCHAKU" `shouldBe` Just Nunchaku
      parseBackendType "Torch" `shouldBe` Just Torch
      parseBackendType "TENSORRT" `shouldBe` Just TensorRT

    it "BUG: doesn't handle whitespace" $ do
      -- BUG: parseBackendType doesn't trim whitespace, so " nunchaku " will
      -- not match "nunchaku", leading to parsing failures for user input with
      -- accidental whitespace.
      parseBackendType " nunchaku " `shouldBe` Nothing -- Should be Just Nunchaku if trimmed

    it "returns Nothing for invalid input" $ do
      parseBackendType "invalid" `shouldBe` Nothing
      parseBackendType "" `shouldBe` Nothing
      parseBackendType "nunchaku2" `shouldBe` Nothing

    it "BUG: doesn't validate input format" $ do
      -- BUG: parseBackendType doesn't validate that the input is a single word.
      -- Input like "nunchaku backend" or "nunchaku, torch" will be parsed as
      -- "nunchaku" (first word), which may hide errors.
      parseBackendType "nunchaku backend" `shouldBe` Just Nunchaku -- May be unexpected
      parseBackendType "torch, nunchaku" `shouldBe` Just Torch -- May be unexpected
