{-|
Module      : Forge.Flag.Flag
Description : Feature Flags

Feature flag system for enabling/disabling functionality at runtime.
Flags are read from environment variables prefixed with FORGE_.

== Environment Variables

| Variable                | Description                    |
|-------------------------|--------------------------------|
| FORGE_DEBUG             | Enable debug mode              |
| FORGE_AUTO_SHARE        | Auto-share sessions            |
| FORGE_STREAMING         | Enable streaming responses     |
| FORGE_EXPERIMENTAL      | Enable experimental features   |
-}
module Forge.Flag.Flag
  ( -- * Flag Checking
    isEnabled
  , isDisabled
  , getEnabled
    -- * Common Flags
  , debugEnabled
  , streamingEnabled
  , experimentalEnabled
    -- * Flag Operations
  , enable
  , disable
  , toggle
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect (Effect)

-- ============================================================================
-- FFI
-- ============================================================================

foreign import getEnvFFI :: String -> Effect (Maybe String)
foreign import setEnvFFI :: String -> String -> Effect Unit
foreign import getAllEnvKeysFFI :: Effect (Array String)

-- ============================================================================
-- FLAG CHECKING
-- ============================================================================

{-| Check if a feature flag is enabled.

Reads from environment variable FORGE_<FLAG> where FLAG is uppercased.
-}
isEnabled :: String -> Effect Boolean
isEnabled flag = do
  let envKey = "FORGE_" <> String.toUpper flag
  envValue <- getEnvFFI envKey
  pure $ case envValue of
    Just "true" -> true
    Just "1" -> true
    Just "yes" -> true
    Just "on" -> true
    _ -> false

{-| Check if a feature flag is disabled. -}
isDisabled :: String -> Effect Boolean
isDisabled flag = do
  enabled <- isEnabled flag
  pure $ not enabled

{-| Get all enabled flags. -}
getEnabled :: Effect (Array String)
getEnabled = do
  keys <- getAllEnvKeysFFI
  let forgeKeys = Array.filter (\k -> String.take 6 k == "FORGE_") keys
  Array.filterA isForgeEnabled forgeKeys
  where
    isForgeEnabled :: String -> Effect Boolean
    isForgeEnabled key = do
      value <- getEnvFFI key
      pure $ case value of
        Just "true" -> true
        Just "1" -> true
        Just "yes" -> true
        Just "on" -> true
        _ -> false

-- ============================================================================
-- COMMON FLAGS
-- ============================================================================

{-| Check if debug mode is enabled. -}
debugEnabled :: Effect Boolean
debugEnabled = isEnabled "DEBUG"

{-| Check if streaming is enabled. -}
streamingEnabled :: Effect Boolean
streamingEnabled = do
  disabled <- isEnabled "NO_STREAMING"
  if disabled
    then pure false
    else pure true  -- Streaming enabled by default

{-| Check if experimental features are enabled. -}
experimentalEnabled :: Effect Boolean
experimentalEnabled = isEnabled "EXPERIMENTAL"

-- ============================================================================
-- FLAG OPERATIONS
-- ============================================================================

{-| Enable a feature flag at runtime. -}
enable :: String -> Effect Unit
enable flag = do
  let envKey = "FORGE_" <> String.toUpper flag
  setEnvFFI envKey "true"

{-| Disable a feature flag at runtime. -}
disable :: String -> Effect Unit
disable flag = do
  let envKey = "FORGE_" <> String.toUpper flag
  setEnvFFI envKey "false"

{-| Toggle a feature flag. -}
toggle :: String -> Effect Boolean
toggle flag = do
  enabled <- isEnabled flag
  if enabled
    then do
      disable flag
      pure false
    else do
      enable flag
      pure true
