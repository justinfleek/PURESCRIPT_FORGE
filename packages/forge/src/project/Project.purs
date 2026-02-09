{-|
Module      : Forge.Project.Project
Description : Project Information

Handles project detection, information gathering, and metadata.
Detects project types from configuration files and directory structure.
-}
module Forge.Project.Project
  ( -- * Types
    ProjectInfo
  , ProjectType(..)
    -- * Project Operations
  , get
  , detect
  , detectType
    -- * Project Queries
  , getName
  , getRoot
  , hasConfig
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Project type
data ProjectType
  = NodeJS
  | TypeScript
  | Rust
  | Go
  | Python
  | Haskell
  | PureScript
  | Generic

derive instance eqProjectType :: Eq ProjectType

instance showProjectType :: Show ProjectType where
  show NodeJS = "nodejs"
  show TypeScript = "typescript"
  show Rust = "rust"
  show Go = "go"
  show Python = "python"
  show Haskell = "haskell"
  show PureScript = "purescript"
  show Generic = "generic"

-- | Project info
type ProjectInfo =
  { root :: String
  , name :: String
  , projectType :: ProjectType
  , gitRoot :: Maybe String
  , configPath :: Maybe String
  , packageManager :: Maybe String
  }

-- ============================================================================
-- FFI
-- ============================================================================

foreign import fileExistsFFI :: String -> Aff Boolean
foreign import findGitRootFFI :: String -> Aff (Maybe String)
foreign import getBaseNameFFI :: String -> String

-- ============================================================================
-- PROJECT OPERATIONS
-- ============================================================================

{-| Get project information for a directory. -}
get :: String -> Aff (Either String ProjectInfo)
get directory = do
  -- Detect project type
  projType <- detectType directory
  
  -- Find git root
  gitRoot <- findGitRootFFI directory
  
  -- Find config file
  configPath <- findConfigPath directory
  
  -- Detect package manager
  pkgManager <- detectPackageManager directory
  
  pure $ Right
    { root: directory
    , name: getBaseNameFFI directory
    , projectType: projType
    , gitRoot
    , configPath
    , packageManager: pkgManager
    }

{-| Detect project from a file path.

Walks up the directory tree to find project root.
-}
detect :: String -> Aff (Maybe ProjectInfo)
detect filePath = do
  -- Find project root by looking for markers
  root <- findProjectRoot filePath
  case root of
    Nothing -> pure Nothing
    Just r -> do
      result <- get r
      case result of
        Left _ -> pure Nothing
        Right info -> pure $ Just info

{-| Detect project type from directory contents. -}
detectType :: String -> Aff ProjectType
detectType directory = do
  -- Check for various project markers
  hasPackageJson <- fileExistsFFI (directory <> "/package.json")
  hasTsConfig <- fileExistsFFI (directory <> "/tsconfig.json")
  hasCargoToml <- fileExistsFFI (directory <> "/Cargo.toml")
  hasGoMod <- fileExistsFFI (directory <> "/go.mod")
  hasPyproject <- fileExistsFFI (directory <> "/pyproject.toml")
  hasSetupPy <- fileExistsFFI (directory <> "/setup.py")
  hasCabal <- fileExistsFFI (directory <> "/*.cabal")
  hasStack <- fileExistsFFI (directory <> "/stack.yaml")
  hasSpago <- fileExistsFFI (directory <> "/spago.yaml")
  hasSpagoDhall <- fileExistsFFI (directory <> "/spago.dhall")
  
  pure $ case unit of
    _ | hasTsConfig -> TypeScript
    _ | hasPackageJson -> NodeJS
    _ | hasCargoToml -> Rust
    _ | hasGoMod -> Go
    _ | hasPyproject || hasSetupPy -> Python
    _ | hasCabal || hasStack -> Haskell
    _ | hasSpago || hasSpagoDhall -> PureScript
    _ -> Generic

-- ============================================================================
-- PROJECT QUERIES
-- ============================================================================

{-| Get project name from info. -}
getName :: ProjectInfo -> String
getName = _.name

{-| Get project root from info. -}
getRoot :: ProjectInfo -> String
getRoot = _.root

{-| Check if project has Forge config. -}
hasConfig :: String -> Aff Boolean
hasConfig directory = fileExistsFFI (directory <> "/.forge/config.json")

-- ============================================================================
-- HELPERS
-- ============================================================================

findConfigPath :: String -> Aff (Maybe String)
findConfigPath directory = do
  hasForgeConfig <- fileExistsFFI (directory <> "/.forge/config.json")
  if hasForgeConfig
    then pure $ Just (directory <> "/.forge/config.json")
    else pure Nothing

detectPackageManager :: String -> Aff (Maybe String)
detectPackageManager directory = do
  hasPnpmLock <- fileExistsFFI (directory <> "/pnpm-lock.yaml")
  hasYarnLock <- fileExistsFFI (directory <> "/yarn.lock")
  hasBunLock <- fileExistsFFI (directory <> "/bun.lockb")
  hasPackageLock <- fileExistsFFI (directory <> "/package-lock.json")
  
  pure $ case unit of
    _ | hasPnpmLock -> Just "pnpm"
    _ | hasYarnLock -> Just "yarn"
    _ | hasBunLock -> Just "bun"
    _ | hasPackageLock -> Just "npm"
    _ -> Nothing

findProjectRoot :: String -> Aff (Maybe String)
findProjectRoot path = do
  -- Try to find git root first
  gitRoot <- findGitRootFFI path
  case gitRoot of
    Just root -> pure $ Just root
    Nothing -> do
      -- Look for package.json or other project markers
      hasMarker <- hasProjectMarker path
      if hasMarker
        then pure $ Just path
        else pure Nothing

hasProjectMarker :: String -> Aff Boolean
hasProjectMarker directory = do
  markers <- traverse (\m -> fileExistsFFI (directory <> "/" <> m)) projectMarkers
  pure $ Array.any identity markers
  where
    projectMarkers = 
      [ "package.json"
      , "Cargo.toml"
      , "go.mod"
      , "pyproject.toml"
      , "spago.yaml"
      , ".forge"
      ]

traverse :: forall a b. (a -> Aff b) -> Array a -> Aff (Array b)
traverse f arr = traverseImpl f arr

foreign import traverseImpl :: forall a b. (a -> Aff b) -> Array a -> Aff (Array b)
