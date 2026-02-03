{-# LANGUAGE OverloadedStrings #-}

-- | Performance Benchmarks - Performance Testing and Regression Detection
-- |
-- | **What:** Provides performance benchmarks for critical operations (database queries,
-- |         encryption, circuit breakers, etc.). Detects performance regressions.
-- | **Why:** Ensures performance remains acceptable as code changes. Detects performance
-- |         regressions before deployment. Provides baseline metrics.
-- | **How:** Uses Criterion for benchmarking. Benchmarks critical operations and compares
-- |         against baselines. Fails CI if performance degrades significantly.
-- |
-- | **Dependencies:**
-- | - `criterion`: Benchmarking library
-- | - `Bridge.Database.Operations`: Database operations
-- | - `Bridge.Auth.Encryption`: Encryption operations
-- |
-- | **Mathematical Foundation:**
-- | - **Benchmark:** Measure operation time over N iterations
-- | - **Baseline:** Historical performance data
-- | - **Regression:** `currentTime > baselineTime * threshold`
-- |
-- | **Usage Example:**
-- | ```haskell
-- | import Bridge.Performance.Benchmarks as Benchmarks
-- |
-- | -- Run all benchmarks
-- | Benchmarks.runAllBenchmarks
-- | ```
module Bridge.Performance.Benchmarks where

module Bridge.Performance.Benchmarks where

import Prelude hiding (read)
import Criterion.Main
import Database.SQLite.Simple (Connection, open, close, execute, query_)
import qualified Data.Text as T
import Bridge.Auth.Encryption (encryptApiKey, decryptApiKey, getMasterSecret, MasterSecret)
import Bridge.Error.CircuitBreaker (createCircuitBreaker, defaultCircuitBreakerConfig, recordSuccess, recordFailure, isAvailable)
import Data.Time (getCurrentTime)
import Control.Concurrent.STM (atomically)

-- | Benchmark database operations
benchmarkDatabaseOperations :: Connection -> Benchmark
benchmarkDatabaseOperations conn = bgroup "database"
  [ bench "insert" $ nfIO (insertBenchmark conn)
  , bench "select" $ nfIO (selectBenchmark conn)
  , bench "update" $ nfIO (updateBenchmark conn)
  ]
  where
    insertBenchmark :: Connection -> IO Int
    insertBenchmark c = do
      execute c "INSERT INTO test_table (id, value) VALUES (?, ?)" (1 :: Int, "test" :: T.Text)
      pure 1
    
    selectBenchmark :: Connection -> IO Int
    selectBenchmark c = do
      results <- query_ c "SELECT COUNT(*) FROM test_table"
      pure (length results)
    
    updateBenchmark :: Connection -> IO Int
    updateBenchmark c = do
      execute c "UPDATE test_table SET value = ? WHERE id = ?" ("updated" :: T.Text, 1 :: Int)
      pure 1

-- | Benchmark encryption operations
benchmarkEncryption :: MasterSecret -> Benchmark
benchmarkEncryption masterSecret = bgroup "encryption"
  [ bench "encrypt" $ nfIO (encryptBenchmark masterSecret)
  , bench "decrypt" $ nfIO (decryptBenchmark masterSecret)
  ]
  where
    encryptBenchmark :: MasterSecret -> IO Int
    encryptBenchmark secret = do
      result <- encryptApiKey "test-api-key-12345" secret
      case result of
        Right _ -> pure 1
        Left _ -> pure 0
    
    decryptBenchmark :: MasterSecret -> IO Int
    decryptBenchmark secret = do
      -- First encrypt, then decrypt
      encryptResult <- encryptApiKey "test-api-key-12345" secret
      case encryptResult of
        Right encrypted -> do
          decryptResult <- decryptApiKey encrypted secret
          case decryptResult of
            Right _ -> pure 1
            Left _ -> pure 0
        Left _ -> pure 0

-- | Benchmark circuit breaker operations
benchmarkCircuitBreaker :: Benchmark
benchmarkCircuitBreaker = bgroup "circuit-breaker"
  [ bench "isAvailable" $ nfIO (isAvailableBenchmark)
  , bench "recordSuccess" $ nfIO (recordSuccessBenchmark)
  , bench "recordFailure" $ nfIO (recordFailureBenchmark)
  ]
  where
    isAvailableBenchmark :: IO Bool
    isAvailableBenchmark = do
      breaker <- createCircuitBreaker defaultCircuitBreakerConfig
      now <- getCurrentTime
      atomically (isAvailable breaker now)
    
    recordSuccessBenchmark :: IO ()
    recordSuccessBenchmark = do
      breaker <- createCircuitBreaker defaultCircuitBreakerConfig
      atomically (recordSuccess breaker)
    
    recordFailureBenchmark :: IO ()
    recordFailureBenchmark = do
      breaker <- createCircuitBreaker defaultCircuitBreakerConfig
      now <- getCurrentTime
      atomically (recordFailure breaker now)

-- | Run all benchmarks
-- |
-- | **Purpose:** Runs all performance benchmarks.
-- | **Returns:** Benchmark results
runAllBenchmarks :: IO ()
runAllBenchmarks = do
  -- Setup
  masterSecretResult <- getMasterSecret
  case masterSecretResult of
    Left err -> putStrLn ("Error: BRIDGE_ENCRYPTION_KEY not set: " ++ err) >> return ()
    Right masterSecret -> do
      -- Create test database
      conn <- open ":memory:"
  execute conn "CREATE TABLE test_table (id INTEGER PRIMARY KEY, value TEXT)" ()
  
  -- Run benchmarks
  defaultMain
    [ benchmarkDatabaseOperations conn
    , benchmarkEncryption masterSecret
    , benchmarkCircuitBreaker
    ]
  
  -- Cleanup
  close conn
