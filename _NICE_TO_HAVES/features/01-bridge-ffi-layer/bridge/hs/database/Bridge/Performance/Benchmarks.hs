{-# LANGUAGE OverloadedStrings #-}

-- | Performance Benchmarks - Performance Testing and Regression Detection
-- |
-- | Provides performance benchmarks for critical operations.
module Bridge.Performance.Benchmarks
  ( runAllBenchmarks
  , BenchmarkResult(..)
  , runQuickBenchmark
  ) where

import Prelude hiding (read)
import Database.SQLite.Simple (Connection, open, close, execute, query_, Only(..))
import qualified Data.Text as T
import Data.Text (Text)
import Bridge.Auth.Encryption (encryptApiKey, decryptApiKey, getMasterSecret, MasterSecret)
import Bridge.Error.CircuitBreaker (createCircuitBreaker, defaultCircuitBreakerConfig, recordSuccess, recordFailure, isAvailable)
import Data.Time (getCurrentTime, diffUTCTime, NominalDiffTime)
import Control.Concurrent.STM (atomically)
import Control.Exception (try, SomeException)

-- | Benchmark result
data BenchmarkResult = BenchmarkResult
  { brName :: Text
  , brIterations :: Int
  , brTotalTime :: NominalDiffTime
  , brAverageTime :: NominalDiffTime
  } deriving (Eq, Show)

-- | Run a quick benchmark (non-Criterion, for simpler builds)
runQuickBenchmark :: Text -> Int -> IO () -> IO BenchmarkResult
runQuickBenchmark name iterations action = do
  startTime <- getCurrentTime
  mapM_ (const action) [1..iterations]
  endTime <- getCurrentTime
  let totalTime = diffUTCTime endTime startTime
  let avgTime = totalTime / fromIntegral iterations
  pure BenchmarkResult
    { brName = name
    , brIterations = iterations
    , brTotalTime = totalTime
    , brAverageTime = avgTime
    }

-- | Benchmark database insert
benchmarkDatabaseInsert :: Connection -> IO ()
benchmarkDatabaseInsert conn = do
  _ <- try (execute conn "INSERT INTO test_table (id, value) VALUES (?, ?)" (1 :: Int, "test" :: T.Text)) :: IO (Either SomeException ())
  pure ()

-- | Benchmark database select
benchmarkDatabaseSelect :: Connection -> IO ()
benchmarkDatabaseSelect conn = do
  _ <- try $ query_ conn "SELECT COUNT(*) FROM test_table" :: IO (Either SomeException [Only Int])
  pure ()

-- | Benchmark encryption
benchmarkEncryption :: MasterSecret -> IO ()
benchmarkEncryption masterSecret = do
  _ <- encryptApiKey "test-api-key-12345" masterSecret
  pure ()

-- | Benchmark circuit breaker isAvailable
benchmarkCircuitBreakerAvailable :: IO ()
benchmarkCircuitBreakerAvailable = do
  breaker <- createCircuitBreaker defaultCircuitBreakerConfig
  now <- getCurrentTime
  _ <- atomically (isAvailable breaker now)
  pure ()

-- | Benchmark circuit breaker recordSuccess
benchmarkCircuitBreakerSuccess :: IO ()
benchmarkCircuitBreakerSuccess = do
  breaker <- createCircuitBreaker defaultCircuitBreakerConfig
  atomically (recordSuccess breaker)

-- | Benchmark circuit breaker recordFailure
benchmarkCircuitBreakerFailure :: IO ()
benchmarkCircuitBreakerFailure = do
  breaker <- createCircuitBreaker defaultCircuitBreakerConfig
  now <- getCurrentTime
  atomically (recordFailure breaker now)

-- | Run all benchmarks
runAllBenchmarks :: IO [BenchmarkResult]
runAllBenchmarks = do
  putStrLn "Running benchmarks..."
  
  -- Setup
  masterSecretResult <- getMasterSecret
  case masterSecretResult of
    Left err -> do
      putStrLn $ "Warning: BRIDGE_ENCRYPTION_KEY not set: " ++ err
      putStrLn "Skipping encryption benchmarks..."
      runBenchmarksWithoutEncryption
    Right masterSecret -> do
      runBenchmarksWithEncryption masterSecret

runBenchmarksWithoutEncryption :: IO [BenchmarkResult]
runBenchmarksWithoutEncryption = do
  -- Create test database
  conn <- open ":memory:"
  _ <- try $ execute conn "CREATE TABLE test_table (id INTEGER PRIMARY KEY, value TEXT)" () :: IO (Either SomeException ())
  
  -- Run benchmarks
  dbInsert <- runQuickBenchmark "database-insert" 100 (benchmarkDatabaseInsert conn)
  dbSelect <- runQuickBenchmark "database-select" 100 (benchmarkDatabaseSelect conn)
  cbAvailable <- runQuickBenchmark "circuit-breaker-available" 1000 benchmarkCircuitBreakerAvailable
  cbSuccess <- runQuickBenchmark "circuit-breaker-success" 1000 benchmarkCircuitBreakerSuccess
  cbFailure <- runQuickBenchmark "circuit-breaker-failure" 1000 benchmarkCircuitBreakerFailure
  
  -- Cleanup
  close conn
  
  let results = [dbInsert, dbSelect, cbAvailable, cbSuccess, cbFailure]
  printResults results
  pure results

runBenchmarksWithEncryption :: MasterSecret -> IO [BenchmarkResult]
runBenchmarksWithEncryption masterSecret = do
  -- Create test database
  conn <- open ":memory:"
  _ <- try $ execute conn "CREATE TABLE test_table (id INTEGER PRIMARY KEY, value TEXT)" () :: IO (Either SomeException ())
  
  -- Run benchmarks
  dbInsert <- runQuickBenchmark "database-insert" 100 (benchmarkDatabaseInsert conn)
  dbSelect <- runQuickBenchmark "database-select" 100 (benchmarkDatabaseSelect conn)
  encryption <- runQuickBenchmark "encryption" 100 (benchmarkEncryption masterSecret)
  cbAvailable <- runQuickBenchmark "circuit-breaker-available" 1000 benchmarkCircuitBreakerAvailable
  cbSuccess <- runQuickBenchmark "circuit-breaker-success" 1000 benchmarkCircuitBreakerSuccess
  cbFailure <- runQuickBenchmark "circuit-breaker-failure" 1000 benchmarkCircuitBreakerFailure
  
  -- Cleanup
  close conn
  
  let results = [dbInsert, dbSelect, encryption, cbAvailable, cbSuccess, cbFailure]
  printResults results
  pure results

printResults :: [BenchmarkResult] -> IO ()
printResults results = do
  putStrLn "\n=== Benchmark Results ==="
  mapM_ printResult results
  putStrLn "========================="
  where
    printResult r = putStrLn $ T.unpack (brName r) ++ ": " ++ 
      show (brIterations r) ++ " iterations, " ++
      "avg " ++ show (brAverageTime r)
