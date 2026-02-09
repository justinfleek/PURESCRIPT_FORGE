{-|
Module      : Forge.Env.Index
Description : Environment variable utilities

Provides access to environment variables with type-safe getters
and common environment checks.

== Common Variables

| Variable       | Description                    |
|----------------|--------------------------------|
| NODE_ENV       | Runtime environment            |
| FORGE_DEBUG    | Enable debug mode              |
| FORGE_LOG      | Log level                      |
| HOME           | User home directory            |
| EDITOR         | Default text editor            |
-}
module Forge.Env.Index
  ( -- * Basic Operations
    get
  , getRequired
  , getWithDefault
  , set
  , unset
    -- * Type-Safe Getters
  , getInt
  , getBool
  , getArray
    -- * Environment Checks
  , isDev
  , isProd
  , isTest
  , isDebug
  , isCI
    -- * Common Variables
  , getHome
  , getEditor
  , getShell
  , getLogLevel
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Effect (Effect)

-- ============================================================================
-- FFI
-- ============================================================================

foreign import getEnvFFI :: String -> Effect (Maybe String)
foreign import setEnvFFI :: String -> String -> Effect Unit
foreign import unsetEnvFFI :: String -> Effect Unit

-- ============================================================================
-- BASIC OPERATIONS
-- ============================================================================

{-| Get an environment variable.

Returns Nothing if the variable is not set.
-}
get :: String -> Effect (Maybe String)
get = getEnvFFI

{-| Get a required environment variable.

Returns an error if the variable is not set.
-}
getRequired :: String -> Effect (Either String String)
getRequired key = do
  result <- get key
  pure $ case result of
    Nothing -> Left ("Required environment variable not set: " <> key)
    Just value -> Right value

{-| Get an environment variable with a default value. -}
getWithDefault :: String -> String -> Effect String
getWithDefault key defaultValue = do
  result <- get key
  pure $ fromMaybe defaultValue result

{-| Set an environment variable. -}
set :: String -> String -> Effect Unit
set = setEnvFFI

{-| Unset an environment variable. -}
unset :: String -> Effect Unit
unset = unsetEnvFFI

-- ============================================================================
-- TYPE-SAFE GETTERS
-- ============================================================================

{-| Get an integer environment variable. -}
getInt :: String -> Effect (Maybe Int)
getInt key = do
  result <- get key
  pure $ result >>= parseIntMaybe
  where
    parseIntMaybe s =
      let n = parseIntFFI s
      in if n >= 0 || String.take 1 s == "-"
         then Just n
         else Nothing

{-| Get a boolean environment variable.

Recognizes: "true", "1", "yes", "on" as true
            "false", "0", "no", "off" as false
-}
getBool :: String -> Effect (Maybe Boolean)
getBool key = do
  result <- get key
  pure $ result >>= parseBool
  where
    parseBool s =
      let lower = String.toLower s
      in if Array.elem lower ["true", "1", "yes", "on"]
         then Just true
         else if Array.elem lower ["false", "0", "no", "off"]
           then Just false
           else Nothing

{-| Get an array environment variable (comma-separated). -}
getArray :: String -> Effect (Array String)
getArray key = do
  result <- get key
  pure $ case result of
    Nothing -> []
    Just value -> 
      value
        # String.split (String.Pattern ",")
        # map String.trim
        # Array.filter (not <<< String.null)

-- ============================================================================
-- ENVIRONMENT CHECKS
-- ============================================================================

{-| Check if running in development mode. -}
isDev :: Effect Boolean
isDev = do
  nodeEnv <- get "NODE_ENV"
  pure $ case nodeEnv of
    Just "development" -> true
    Just "dev" -> true
    _ -> false

{-| Check if running in production mode. -}
isProd :: Effect Boolean
isProd = do
  nodeEnv <- get "NODE_ENV"
  pure $ case nodeEnv of
    Just "production" -> true
    Just "prod" -> true
    _ -> false

{-| Check if running in test mode. -}
isTest :: Effect Boolean
isTest = do
  nodeEnv <- get "NODE_ENV"
  pure $ case nodeEnv of
    Just "test" -> true
    Just "testing" -> true
    _ -> false

{-| Check if debug mode is enabled. -}
isDebug :: Effect Boolean
isDebug = do
  debug <- getBool "FORGE_DEBUG"
  pure $ fromMaybe false debug

{-| Check if running in CI environment. -}
isCI :: Effect Boolean
isCI = do
  ci <- get "CI"
  githubActions <- get "GITHUB_ACTIONS"
  pure $ case ci of
    Just _ -> true
    Nothing -> case githubActions of
      Just _ -> true
      Nothing -> false

-- ============================================================================
-- COMMON VARIABLES
-- ============================================================================

{-| Get user home directory. -}
getHome :: Effect (Maybe String)
getHome = do
  home <- get "HOME"
  case home of
    Just h -> pure $ Just h
    Nothing -> get "USERPROFILE"  -- Windows

{-| Get default text editor. -}
getEditor :: Effect String
getEditor = getWithDefault "EDITOR" "vim"

{-| Get user shell. -}
getShell :: Effect String
getShell = getWithDefault "SHELL" "/bin/sh"

{-| Get log level. -}
getLogLevel :: Effect String
getLogLevel = getWithDefault "FORGE_LOG" "info"

-- ============================================================================
-- FFI HELPERS
-- ============================================================================

foreign import parseIntFFI :: String -> Int
