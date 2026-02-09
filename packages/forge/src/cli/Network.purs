{-|
Module      : Forge.CLI.Network
Description : CLI Network utilities

Network utilities for the CLI including server availability checks
and port finding.
-}
module Forge.CLI.Network
  ( -- * Types
    NetworkConfig
  , ServerStatus(..)
    -- * Server Operations
  , checkServer
  , checkServerWithTimeout
  , waitForServer
    -- * Port Operations
  , findAvailablePort
  , isPortAvailable
    -- * Default Config
  , defaultConfig
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff, delay)
import Data.Time.Duration (Milliseconds(..))

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Network configuration
type NetworkConfig =
  { host :: String
  , port :: Int
  , timeout :: Int  -- milliseconds
  }

-- | Server status
data ServerStatus
  = ServerUp
  | ServerDown String  -- reason
  | ServerTimeout

derive instance eqServerStatus :: Eq ServerStatus

instance showServerStatus :: Show ServerStatus where
  show ServerUp = "up"
  show (ServerDown reason) = "down: " <> reason
  show ServerTimeout = "timeout"

-- ============================================================================
-- FFI
-- ============================================================================

-- | Check server via HTTP request
foreign import checkServerFFI :: String -> Int -> Aff (Either String Int)

-- | Check if port is available
foreign import isPortAvailableFFI :: Int -> Aff Boolean

-- | Find available port starting from given port
foreign import findAvailablePortFFI :: Int -> Int -> Aff Int

-- ============================================================================
-- DEFAULT CONFIG
-- ============================================================================

-- | Default network configuration
defaultConfig :: NetworkConfig
defaultConfig =
  { host: "localhost"
  , port: 3000
  , timeout: 5000
  }

-- ============================================================================
-- SERVER OPERATIONS
-- ============================================================================

{-| Check if a server is available.

Makes an HTTP request to the given URL and checks for a successful response.
-}
checkServer :: String -> Aff (Either String Boolean)
checkServer url = checkServerWithTimeout url 5000

{-| Check server with custom timeout. -}
checkServerWithTimeout :: String -> Int -> Aff (Either String Boolean)
checkServerWithTimeout url timeout = do
  result <- checkServerFFI url timeout
  case result of
    Left err -> pure $ Left err
    Right statusCode -> 
      if statusCode >= 200 && statusCode < 400
        then pure $ Right true
        else pure $ Left ("Server returned status " <> show statusCode)

{-| Wait for a server to become available.

Retries until the server is up or max retries is reached.
-}
waitForServer :: String -> Int -> Int -> Aff ServerStatus
waitForServer url maxRetries delayMs = go maxRetries
  where
    go :: Int -> Aff ServerStatus
    go 0 = pure ServerTimeout
    go n = do
      result <- checkServer url
      case result of
        Right true -> pure ServerUp
        Right false -> retry n
        Left _ -> retry n
    
    retry :: Int -> Aff ServerStatus
    retry n = do
      delay (Milliseconds (toNumber delayMs))
      go (n - 1)

-- ============================================================================
-- PORT OPERATIONS
-- ============================================================================

{-| Find an available port starting from the given port.

Searches up to 100 ports from the starting port.
-}
findAvailablePort :: Int -> Aff (Either String Int)
findAvailablePort startPort = do
  port <- findAvailablePortFFI startPort 100
  if port > 0
    then pure $ Right port
    else pure $ Left ("No available port found starting from " <> show startPort)

{-| Check if a specific port is available. -}
isPortAvailable :: Int -> Aff Boolean
isPortAvailable = isPortAvailableFFI

-- ============================================================================
-- HELPERS
-- ============================================================================

toNumber :: Int -> Number
toNumber = toNumberFFI

foreign import toNumberFFI :: Int -> Number
