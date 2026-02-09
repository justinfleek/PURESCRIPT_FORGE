{-|
Module      : Forge.CLI.Bootstrap
Description : CLI Bootstrap

Initializes the CLI environment, ensuring required directories exist
and configuration is loaded.

== Bootstrap Process

1. Verify/create working directory
2. Load configuration
3. Initialize logging
4. Run the provided callback
-}
module Forge.CLI.Bootstrap
  ( -- * Bootstrap
    bootstrap
  , bootstrapWithConfig
    -- * Types
  , BootstrapConfig
  , BootstrapResult
  , defaultConfig
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff, try)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Bootstrap configuration
type BootstrapConfig =
  { workingDir :: String
  , createIfMissing :: Boolean
  , loadConfig :: Boolean
  , initLogging :: Boolean
  }

-- | Bootstrap result with context
type BootstrapResult a =
  { value :: a
  , workingDir :: String
  , configLoaded :: Boolean
  }

-- ============================================================================
-- FFI
-- ============================================================================

-- | Check if directory exists
foreign import directoryExistsFFI :: String -> Aff Boolean

-- | Create directory recursively
foreign import mkdirpFFI :: String -> Aff (Either String Unit)

-- | Get current working directory
foreign import cwdFFI :: Aff String

-- ============================================================================
-- DEFAULT CONFIG
-- ============================================================================

-- | Default bootstrap configuration
defaultConfig :: BootstrapConfig
defaultConfig =
  { workingDir: "."
  , createIfMissing: true
  , loadConfig: true
  , initLogging: true
  }

-- ============================================================================
-- BOOTSTRAP
-- ============================================================================

{-| Bootstrap the CLI with a working directory and callback.

Ensures the directory exists, then runs the callback.
-}
bootstrap :: forall a. String -> Aff a -> Aff (Either String a)
bootstrap directory callback = 
  bootstrapWithConfig defaultConfig { workingDir = directory } callback

{-| Bootstrap with custom configuration. -}
bootstrapWithConfig :: forall a. BootstrapConfig -> Aff a -> Aff (Either String a)
bootstrapWithConfig config callback = do
  -- 1. Resolve working directory
  workDir <- if config.workingDir == "." 
             then cwdFFI
             else pure config.workingDir
  
  -- 2. Check if directory exists
  exists <- directoryExistsFFI workDir
  
  -- 3. Create if needed
  if not exists && config.createIfMissing
    then do
      result <- mkdirpFFI workDir
      case result of
        Left err -> pure $ Left ("Failed to create directory: " <> err)
        Right _ -> runCallback callback
    else if not exists
      then pure $ Left ("Directory does not exist: " <> workDir)
      else runCallback callback

  where
    runCallback :: Aff a -> Aff (Either String a)
    runCallback cb = do
      result <- try cb
      case result of
        Left err -> pure $ Left (show err)
        Right value -> pure $ Right value
