{-# LANGUAGE OverloadedStrings #-}

-- | Bridge Performance Benchmarks
-- |
-- | Criterion-based benchmark suite for measuring performance
-- | of database operations, encryption, and circuit breaker.
-- |
-- | Dependencies:
-- | - Criterion.Main: Benchmarking framework
-- | - Database.SQLite.Simple: Database operations
-- | - Bridge.Auth.Encryption: Encryption benchmarks
-- | - Bridge.Error.CircuitBreaker: Circuit breaker benchmarks
module Bridge.Performance.Benchmarks where

import Criterion.Main
  ( Benchmark
  , bench
  , bgroup
  , defaultMain
  , nfIO
  , whnfIO
  )
import Database.SQLite.Simple
  ( Connection
  , open
  , close
  , execute_
  , execute
  , query
  , Only(..)
  )
import Bridge.Auth.Encryption
  ( encryptApiKey
  , decryptApiKey
  , EncryptionResult(..)
  )
import Bridge.Error.CircuitBreaker
  ( CircuitBreakerConfig(..)
  , defaultCircuitBreakerConfig
  , createCircuitBreaker
  , recordSuccess
  , recordFailure
  , isAvailable
  )
import Control.Concurrent.STM (atomically)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Time (getCurrentTime)

-- | Benchmark database operations
-- |
-- | Tests:
-- | - INSERT performance
-- | - SELECT by primary key
-- | - SELECT with index scan
-- | - UPDATE performance
-- | - DELETE performance
benchmarkDatabaseOperations :: IO [Benchmark]
benchmarkDatabaseOperations = do
  conn <- open ":memory:"

  -- Setup schema
  execute_ conn "CREATE TABLE IF NOT EXISTS bench_data (\
    \id INTEGER PRIMARY KEY AUTOINCREMENT,\
    \key TEXT NOT NULL,\
    \value TEXT NOT NULL,\
    \timestamp TEXT NOT NULL\
    \)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_bench_key ON bench_data(key)"

  -- Pre-populate for read benchmarks
  mapM_ (\i -> execute conn
    "INSERT INTO bench_data (key, value, timestamp) VALUES (?, ?, datetime('now'))"
    ("key-" <> T.pack (show (i :: Int)), "value-" <> T.pack (show i))
    ) [1..1000]

  pure
    [ bgroup "database"
        [ bench "insert" $ nfIO (execute conn
            "INSERT INTO bench_data (key, value, timestamp) VALUES (?, ?, datetime('now'))"
            ("bench-key" :: Text, "bench-value" :: Text))
        , bench "select-by-key" $ nfIO (query conn
            "SELECT id, key, value, timestamp FROM bench_data WHERE key = ?"
            (Only ("key-500" :: Text)) :: IO [(Int, Text, Text, Text)])
        , bench "select-range" $ nfIO (query conn
            "SELECT id, key, value, timestamp FROM bench_data WHERE id BETWEEN ? AND ?"
            (100 :: Int, 200 :: Int) :: IO [(Int, Text, Text, Text)])
        , bench "update" $ nfIO (execute conn
            "UPDATE bench_data SET value = ? WHERE key = ?"
            ("updated-value" :: Text, "key-500" :: Text))
        , bench "delete-insert" $ nfIO (do
            execute conn "DELETE FROM bench_data WHERE key = ?" (Only ("key-999" :: Text))
            execute conn
              "INSERT INTO bench_data (key, value, timestamp) VALUES (?, ?, datetime('now'))"
              ("key-999" :: Text, "value-999" :: Text))
        ]
    ]

-- | Benchmark encryption operations
-- |
-- | Tests:
-- | - API key encryption throughput
-- | - API key decryption throughput
-- | - Round-trip (encrypt then decrypt)
benchmarkEncryption :: IO [Benchmark]
benchmarkEncryption = do
  let masterSecret = "benchmark-master-secret-32bytes!"
  let testApiKey = "sk-test-api-key-for-benchmarking-1234567890"

  -- Pre-encrypt for decryption benchmark
  encResult <- encryptApiKey testApiKey masterSecret
  case encResult of
    Left err -> do
      putStrLn ("Encryption setup failed: " ++ err)
      pure []
    Right encrypted ->
      pure
        [ bgroup "encryption"
            [ bench "encrypt" $ nfIO (encryptApiKey testApiKey masterSecret)
            , bench "decrypt" $ nfIO (decryptApiKey encrypted masterSecret)
            , bench "round-trip" $ nfIO (do
                result <- encryptApiKey testApiKey masterSecret
                case result of
                  Left _ -> pure (Left "encrypt failed")
                  Right enc -> decryptApiKey enc masterSecret)
            ]
        ]

-- | Benchmark circuit breaker operations
-- |
-- | Tests:
-- | - recordSuccess throughput
-- | - recordFailure throughput
-- | - isAvailable check throughput
-- | - State transition (closed -> open -> half-open)
benchmarkCircuitBreaker :: IO [Benchmark]
benchmarkCircuitBreaker = do
  now <- getCurrentTime
  cb <- atomically (createCircuitBreaker now defaultCircuitBreakerConfig)

  pure
    [ bgroup "circuit-breaker"
        [ bench "record-success" $ whnfIO (atomically (recordSuccess cb))
        , bench "record-failure" $ whnfIO (do
            t <- getCurrentTime
            atomically (recordFailure cb t))
        , bench "is-available" $ whnfIO (do
            t <- getCurrentTime
            atomically (isAvailable cb t))
        , bench "state-transition" $ nfIO (do
            t <- getCurrentTime
            cb' <- atomically (createCircuitBreaker t CircuitBreakerConfig
              { cbcFailureThreshold = 0.01
              , cbcSuccessThreshold = 1
              , cbcTimeoutSeconds = 0
              , cbcWindowSize = 10
              })
            -- Force open by recording failures
            atomically (recordFailure cb' t)
            atomically (recordFailure cb' t)
            -- Check availability (should transition to half-open since timeout=0)
            t2 <- getCurrentTime
            atomically (isAvailable cb' t2))
        ]
    ]

-- | Run all benchmarks
-- |
-- | Collects all benchmark groups and runs them with Criterion.
runAllBenchmarks :: IO ()
runAllBenchmarks = do
  dbBenches <- benchmarkDatabaseOperations
  encBenches <- benchmarkEncryption
  cbBenches <- benchmarkCircuitBreaker
  defaultMain (dbBenches ++ encBenches ++ cbBenches)
